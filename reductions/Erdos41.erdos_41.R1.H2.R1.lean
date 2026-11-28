import OMAReductions.R_Erdos41_erdos_41_R1
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Data.Nat.Log

/-!
# A finite formulation of Erdős problem 41

H1 asks whether sufficiently many occupied geometric intervals force a finite B₃ set
to have more than C u² pairs at distance at most u³ for some scale u in a finite range.
The lemma `finite_packing` proves H2. The theorem `erdos41_iff_finite_short_pairs`
proves that H1 is equivalent to the exact original conjecture. Its forward implication
uses compactness of the space of characteristic functions.
-/

-- Credit: @Iraeeee
-- The short-pair estimate uses the signed-triple translation argument of
-- @mucoucah (open-math-agents PR 8251). The cubic count is from @ysanatomic.

open Set Filter

namespace OMA.R_Erdos41_erdos_41_R1_H2_R1

/-- The finite extremal question. Every occupied block has a prescribed minimum
size. A sufficiently long run of such blocks should force too many short pairs
at some resolution in a finite range. -/
def H1 : Prop :=
  ∀ q C b u₀ : ℕ, 4 ≤ q → 0 < C → ∃ h : ℕ, ∀ S : Finset ℕ,
    (∀ x ∈ S, x ≤ (q^(b+h+1))^3) →
    Erdos41.NtupleCondition (S : Set ℕ) 3 →
    (∀ j : ℕ, b ≤ j → j ≤ b+h → q^j ≤
      (S.filter (fun x => 8*(q^j)^3 < x ∧ x ≤ (q^(j+1))^3)).card) →
    ∃ u : ℕ, u₀ ≤ u ∧ u ≤ q^(b+h+1) ∧
      C*u^2 < ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 ≤ p.1+u^3)).card

/-- A finite upper bound: translate each short difference by the anchors in T.
A reduced signed triple has at most two possible orders for its positive terms. -/
def H2 : Prop :=
  ∀ (T S : Finset ℕ) (H r : ℕ),
    Erdos41.NtupleCondition ((T : Set ℕ) ∪ (S : Set ℕ)) 3 →
    (∀ a ∈ T, a ≤ H) →
    (T.card-1)*((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 ≤ p.1+r)).card ≤
      2*(H+r+1)


/-- The finite packing half follows from the injectivity of reduced signed triples. -/
theorem finite_packing : H2 := by
  classical
  intro T S H r hB hT
  let P := (S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 ≤ p.1+r)
  let D := P.sigma (fun p => T.erase p.2)
  let F (z : (p : ℕ × ℕ) × ℕ) : Bool × ℕ :=
    (decide (z.2 ≤ z.1.1), z.2 + z.1.1 + r - z.1.2)
  have hdata {x y a : ℕ} (h : Sigma.mk (x,y) a ∈ D) :
      x ∈ S ∧ y ∈ S ∧ x < y ∧ y ≤ x+r ∧ a ≠ y ∧ a ∈ T := by
    obtain ⟨hp,ha⟩ := Finset.mem_sigma.mp h
    obtain ⟨hxy,hlt,hr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    exact ⟨hx,hy,hlt,hr,(Finset.mem_erase.mp ha).1,(Finset.mem_erase.mp ha).2⟩
  have hmaps : Set.MapsTo F (D : Set _) (↑((Finset.univ : Finset Bool) ×ˢ Finset.Iic (H+r) : Finset (Bool × ℕ)) : Set _) := by
    rintro ⟨⟨x,y⟩,a⟩ hz
    obtain ⟨_,_,hxy,_,_,ha⟩ := hdata hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_Iic.mpr ?_⟩
    have := hT a ha
    change a+x+r-y ≤ H+r
    omega
  have hinj : Set.InjOn F (D : Set _) := by
    rintro ⟨⟨x,y⟩,a⟩ ht ⟨⟨u,v⟩,b⟩ hz heq
    obtain ⟨hx,hy,hxy,hyr,hay,ha⟩ := hdata ht
    obtain ⟨hu,hv,huv,hvr,hbv,hb⟩ := hdata hz
    have htag := congrArg Prod.fst heq
    change decide (a ≤ x) = decide (b ≤ u) at htag
    have hval := congrArg Prod.snd heq
    change a+x+r-y = b+u+r-v at hval
    by_cases hax : a ≤ x
    · have hbu : b ≤ u := by simpa [hax] using htag.symm
      obtain ⟨rfl,rfl,rfl⟩ := OMA.R_Erdos41_erdos_41_R1.reduced_signed_eq hB
        (Or.inl ha) (Or.inr hx) (Or.inr hy) (Or.inl hb) (Or.inr hu) (Or.inr hv)
        hax hbu hay.symm hxy.ne' (by omega)
      rfl
    · have hbu : ¬ b ≤ u := by simpa [hax] using htag.symm
      obtain ⟨rfl,rfl,rfl⟩ := OMA.R_Erdos41_erdos_41_R1.reduced_signed_eq hB
        (Or.inr hx) (Or.inl ha) (Or.inr hy) (Or.inr hu) (Or.inl hb) (Or.inr hv)
        (le_of_not_ge hax) (le_of_not_ge hbu) hxy.ne' hay.symm (by omega)
      rfl
  have hcap := Finset.card_le_card_of_injOn F hmaps hinj
  have hsum := Finset.sum_le_sum (s := P) (fun (p : ℕ × ℕ) _ =>
    (Finset.pred_card_le_card_erase : T.card-1 ≤ (T.erase p.2).card))
  rw [Finset.sum_const,smul_eq_mul,Nat.mul_comm] at hsum
  change (T.card-1)*P.card ≤ 2*(H+r+1)
  apply hsum.trans
  simpa [D,Finset.card_sigma] using hcap

lemma b3_subset {A B : Set ℕ} (hB : Erdos41.NtupleCondition B 3) (hAB : A ⊆ B) :
    Erdos41.NtupleCondition A 3 := by
  intro I J hI hJ
  exact hB I J (fun i hi => hAB (hI i hi)) (fun j hj => hAB (hJ j hj))

lemma count_first {f : ℕ → ℕ} (hf : StrictMono f) {n Y : ℕ} (hn : f n ≤ Y) :
    n ≤ (range f ∩ Icc 1 Y).ncard := by
  have hsub : f '' Icc 1 n ⊆ range f ∩ Icc 1 Y := by
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨mem_range_self _,hi.1.trans (hf.id_le i),(hf.monotone hi.2).trans hn⟩
  simpa [Set.ncard_image_of_injective _ hf.injective] using
    (Set.ncard_le_ncard hsub ((Set.finite_Icc ..).subset inter_subset_right))

lemma count_annulus (A : Set ℕ) {X Y : ℕ} (h : X ≤ Y) :
    (A ∩ Icc 1 Y).ncard = (A ∩ Icc 1 X).ncard + (A ∩ Ioc X Y).ncard := by
  have hU : A ∩ Icc 1 Y = (A ∩ Icc 1 X) ∪ (A ∩ Ioc X Y) := by
    ext n
    simp only [mem_union,mem_inter_iff,mem_Icc,mem_Ioc]
    by_cases ha : n ∈ A
    · simp [ha]
      omega
    · simp [ha]
  rw [hU, Set.ncard_union_eq]
  exact Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2.2) hy.2.1

lemma occupied {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (range f) 3)
    {K n₀ : ℕ} (hk : ∀ i ≥ n₀, f i ≤ K*(i+1)^3) {L : ℕ} (hL : 0 < L) (hn : n₀ ≤ L) :
    L ≤ (range f ∩ Ioc (8*L^3) ((16*(K+1)*L)^3)).ncard := by
  let a := (range f ∩ Icc 1 (8*L^3)).ncard
  have ha : a^3 ≤ 6*(3*(8*L^3)+1) := OMA.R_Erdos41_erdos_41_R1.cubic_count _ hB _
  have hcube : 1 ≤ L^3 := Nat.pow_pos hL
  have hsmall : a ≤ 6*L := by
    apply (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp
    nlinarith only [ha,hcube]
  have hupper := hk (8*L) (by omega)
  have h1 := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (show 8*L+1 ≤ 9*L by omega) 3)
  have h2 : K*(9*L)^3 ≤ (16*(K+1)*L)^3 := by
    have hK : K ≤ (K+1)^3 := (Nat.le_succ K).trans (Nat.le_self_pow (by decide) _)
    have hKL := Nat.mul_le_mul_right ((9*L)^3) hK
    have hh := Nat.pow_le_pow_left (show (K+1)*(9*L) ≤ 16*(K+1)*L by
      nlinarith only [Nat.zero_le (K*L), Nat.zero_le L]) 3
    rw [mul_pow] at hh
    exact hKL.trans hh
  have hbig := count_first hf (hupper.trans (h1.trans h2))
  have hxy : 8*L^3 ≤ (16*(K+1)*L)^3 := by
    have hlocal : 2*L ≤ 16*(K+1)*L := by nlinarith only [Nat.zero_le (K*L), Nat.zero_le L]
    simpa [mul_pow] using Nat.pow_le_pow_left hlocal 3
  rw [count_annulus _ hxy] at hbig
  dsimp only [a] at hsmall
  omega

lemma impossible_cubic_bound (hfinite : H1) (hpacking : H2) {f : ℕ → ℕ}
    (hf : StrictMono f) (hk : ∃ K : ℕ, ∀ᶠ n : ℕ in atTop, f n ≤ K*(n+1)^3) :
    ¬ Erdos41.NtupleCondition (range f) 3 := by
  classical
  obtain ⟨K,hk⟩ := hk
  intro hB
  obtain ⟨n₀,hk⟩ := eventually_atTop.mp hk
  let q := 16*(K+1)
  let d := 2*(K+1)
  let C := 2*(d^3+2)
  let b := n₀+1
  obtain ⟨h,hh⟩ := hfinite q C b b (by dsimp [q]; omega) (by dsimp [C]; omega)
  let N := (q^(b+h+1))^3
  let S := (Finset.Icc 1 N).filter (· ∈ range f)
  have hS {x : ℕ} : x ∈ S ↔ (1 ≤ x ∧ x ≤ N) ∧ x ∈ range f := by simp [S]
  obtain ⟨u,hu,_,hexcess⟩ := hh S (fun _ hx => (hS.mp hx).1.2)
    (b3_subset hB (fun _ hx => (hS.mp hx).2)) (by
      intro j hj hje
      let L := q^j
      let X := 8*L^3
      let Y := (q^(j+1))^3
      have hq : 2 ≤ q := by dsimp [q]; omega
      have hLp : 0 < L := Nat.pow_pos (by omega : 0 < q)
      have hLj : j ≤ L := (show j < 2^j from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hq _)
      have hok := occupied hf hB hk hLp (by dsimp [b] at hj; omega)
      have hY : Y = (16*(K+1)*L)^3 := by dsimp [Y,L,q]; rw [pow_succ]; ring
      have hYN : Y ≤ N := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega : 0 < q) (by omega)) 3
      have hset : ((S.filter (fun x => X < x ∧ x ≤ Y) : Finset ℕ) : Set ℕ) = range f ∩ Ioc X Y := by
        ext x
        simp only [Finset.mem_coe,Finset.mem_filter,hS,mem_inter_iff,mem_Ioc]
        constructor
        · exact fun hx => ⟨hx.1.2,hx.2⟩
        · exact fun hx => ⟨⟨⟨by omega,hx.2.2.trans hYN⟩,hx.1⟩,hx.2⟩
      change L ≤ (S.filter (fun x => X < x ∧ x ≤ Y)).card
      rw [← Set.ncard_coe_finset,hset,hY]
      exact hok)
  have hu0 : 0 < u := by dsimp [b] at hu; omega
  let T := (Finset.range (u+1)).image f
  have hT : T.card = u+1 := by simp [T, Finset.card_image_of_injective _ hf.injective]
  have htmem {x : ℕ} (hx : x ∈ T) : ∃ i ≤ u, f i = x := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i,Nat.le_of_lt_succ (Finset.mem_range.mp hi),rfl⟩
  have hab : f u ≤ (d*u)^3 := by
    have ha := hk u (by dsimp [b] at hu; omega)
    have hb := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (show u+1 ≤ 2*u by omega) 3)
    have hc := Nat.mul_le_mul_right ((2*u)^3) ((Nat.le_succ K).trans (Nat.le_self_pow (by decide : 3 ≠ 0) _))
    calc
      f u ≤ K*(2*u)^3 := ha.trans hb
      _ ≤ (K+1)^3*(2*u)^3 := hc
      _ = (d*u)^3 := by dsimp [d]; ring
  have hpack := hpacking T S ((d*u)^3) (u^3) (b3_subset hB (by
    rintro x (hx | hx)
    · obtain ⟨i,_,rfl⟩ := htmem hx
      exact mem_range_self _
    · exact (hS.mp hx).2)) (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := htmem hx
      exact (hf.monotone hi).trans hab)
  rw [hT, Nat.add_sub_cancel] at hpack
  have hup : 2*((d*u)^3+u^3+1) ≤ u*(C*u^2) := by
    dsimp [C]
    nlinarith only [show 1 ≤ u^3 from Nat.pow_pos hu0]
  exact (not_lt_of_ge (hpack.trans hup)) (Nat.mul_lt_mul_of_pos_left hexcess hu0)


theorem main : H1 → H2 → OMA.R_Erdos41_erdos_41_R1.H2 := by
  intro hfinite hpacking f hf hk _ _
  exact impossible_cubic_bound hfinite hpacking hf hk

/-- Diagonal extraction on the characteristic functions. On every fixed finite
set of integers the indicators eventually agree with those of the limit set. -/
lemma extract (S : ℕ → Finset ℕ) : ∃ A : Set ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ E : Finset ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ E, (x ∈ S (φ n) ↔ x ∈ A) := by
  classical
  let F (n x : ℕ) := decide (x ∈ S n)
  obtain ⟨a,φ,hφ,ha⟩ := CompactSpace.tendsto_subseq F
  refine ⟨{x | a x = true},φ,hφ,fun E => (Filter.eventually_all_finset E).2 ?_⟩
  intro x _
  have hx := tendsto_pi_nhds.mp ha x
  have he := hx.eventually (isOpen_discrete ({a x} : Set Bool) |>.mem_nhds (Set.mem_singleton (a x)))
  filter_upwards [he] with n hn
  change decide (x ∈ S (φ n)) = a x at hn
  rw [← hn, decide_eq_true_eq]

open Set Filter

lemma finite_of_liminf
    (target : ∀ A : Set ℕ, Erdos41.NtupleCondition A 3 → A.Infinite →
      atTop.liminf (fun n : ℕ => ((A ∩ Icc 1 n).ncard : ℝ)/(n:ℝ)^(1/3:ℝ)) = 0) :
    OMA.R_Erdos41_erdos_41_R1_H2_R1.H1 := by
  classical
  intro q C b u₀ hq hC
  by_contra! hno
  choose S hs using hno
  obtain ⟨A,φ,hφ,hagree⟩ := extract S
  have hB : Erdos41.NtupleCondition A 3 := by
    intro I J hI hJ hi hj heq
    obtain ⟨n, hn⟩ := (hagree (I.toFinset ∪ J.toFinset)).exists
    apply (hs (φ n)).2.1 I J _ _ hi hj heq
    · exact fun i hi => (hn i (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hi))).2 (hI i hi)
    · exact fun i hi => (hn i (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hi))).2 (hJ i hi)
  have hcnt (j : ℕ) (hj : b ≤ j) :
      q^j ≤ (A ∩ Icc 1 ((q^(j+1))^3)).ncard := by
    let Y := (q^(j+1))^3
    let E := Finset.Icc 1 Y
    obtain ⟨n,hn,hφn⟩ := ((hagree E).and (hφ.tendsto_atTop.eventually_ge_atTop j)).exists
    let B := (S (φ n)).filter (fun x => 8*(q^j)^3 < x ∧ x ≤ (q^(j+1))^3)
    have hb : q^j ≤ B.card := (hs (φ n)).2.2.1 j hj (by omega)
    have hsub : (B : Set ℕ) ⊆ A ∩ Icc 1 Y := by
      intro x hx
      obtain ⟨hsx,hxlo,hxhi⟩ := Finset.mem_filter.mp hx
      have hxE : 1 ≤ x ∧ x ≤ Y := ⟨by omega,hxhi⟩
      exact ⟨(hn x (Finset.mem_Icc.mpr hxE)).1 hsx,hxE⟩
    have hc := Set.ncard_le_ncard hsub ((Set.finite_Icc ..).subset inter_subset_right)
    rw [Set.ncard_coe_finset] at hc
    exact hb.trans hc
  have hA : A.Infinite := by
    intro hfin
    let j := max b A.ncard
    have hc := hcnt j (le_max_left ..)
    have hle := Set.ncard_le_ncard (inter_subset_left (s := A) (t := Icc 1 ((q^(j+1))^3))) hfin
    have hjq : j < q^j := (show j < 2^j from Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by omega) _)
    have := le_max_right b A.ncard
    change A.ncard ≤ j at this
    omega
  have hq0 : 0 < q := by omega
  let Q := q^3
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (by decide : 1 < 4^3).trans_le (Nat.pow_le_pow_left hq 3)
  have hscale : ∀ᶠ n : ℕ in atTop, n ≤ (q^2*(A ∩ Icc 1 n).ncard)^3 := by
    filter_upwards [eventually_ge_atTop (Q^(b+1)), eventually_gt_atTop 0] with n hn hn0
    let j := Nat.log Q n - 1
    have he : b+1 ≤ Nat.log Q n := (Nat.le_log_iff_pow_le hQ hn0.ne').2 hn
    have hindex : j+1 = Nat.log Q n := by dsimp [j]; omega
    have hpow (k : ℕ) : (q^k)^3 = Q^k := by dsimp [Q]; rw [← pow_mul, mul_comm, pow_mul]
    have hlow : (q^(j+1))^3 ≤ n := by rw [hpow,hindex]; exact Nat.pow_log_le_self _ hn0.ne'
    have hupper : n ≤ (q^(j+2))^3 := by
      rw [hpow, show j+2 = (Nat.log Q n).succ by omega]
      exact (Nat.lt_pow_succ_log_self hQ n).le
    have hle : (A ∩ Icc 1 ((q^(j+1))^3)).ncard ≤ (A ∩ Icc 1 n).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_inter_right A (Set.Icc_subset_Icc_right hlow))
        ((Set.finite_Icc ..).subset inter_subset_right)
    have hcount := (hcnt j (by dsimp [j]; omega)).trans hle
    apply hupper.trans
    apply Nat.pow_le_pow_left
    rw [pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hcount
  have hqr : (0:ℝ) < q := by exact_mod_cast hq0
  have hr : ∀ᶠ n : ℕ in atTop, (1:ℝ)/(q:ℝ)^2 ≤
      ((A ∩ Icc 1 n).ncard : ℝ)/(n:ℝ)^(1/3:ℝ) := by
    filter_upwards [hscale,eventually_gt_atTop 0] with n hn hnpos
    have hn' : (0:ℝ) < n := by exact_mod_cast hnpos
    have hroot : ((n:ℝ)^(1/3:ℝ))^3 = n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
      norm_num
    have hle : (n:ℝ)^(1/3:ℝ) ≤ (q:ℝ)^2 * (A ∩ Icc 1 n).ncard := by
      apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
      rw [hroot]
      exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) (Real.rpow_pos_of_pos hn' _)]
    linarith
  have hlim := le_liminf_of_le (OMA.R_Erdos41_erdos_41_R1.upper_ratio A hB) hr
  rw [target A hB hA] at hlim
  exact (not_le_of_gt (by positivity : (0:ℝ) < 1/(q:ℝ)^2)) hlim

lemma upper_cubic {f : ℕ → ℕ} (hf : StrictMono f)
    (hpos : 0 < atTop.liminf (fun n : ℕ =>
      ((Set.range f ∩ Icc 1 n).ncard : ℝ) / (n : ℝ)^(1/3 : ℝ))) :
    ∃ K n₀ : ℕ, ∀ n ≥ n₀, f n ≤ K*(n+1)^3 := by
  obtain ⟨K,n₀,_,h⟩ := OMA.R_Erdos41_erdos_41_R1.eventual_cubic_of_pos _ hpos
  refine ⟨K,n₀,fun n hn => ?_⟩
  have hsub : Set.range f ∩ Icc 1 (f n) ⊆ f '' Iic n := by
    rintro x ⟨⟨i,rfl⟩,hx⟩
    exact ⟨i,hf.le_iff_le.mp hx.2,rfl⟩
  have hh := Set.ncard_le_ncard hsub ((Set.finite_Iic n).image f)
  have hh' : (Set.range f ∩ Icc 1 (f n)).ncard ≤ n+1 := by
    simpa [Set.ncard_image_of_injective _ hf.injective] using hh
  exact (h (f n) (hn.trans (hf.id_le n))).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hh' 3))


/-- The finite obstruction is equivalent to the original infinite B₃ conjecture. -/
theorem erdos41_iff_finite_short_pairs :
    (type_of% @Erdos41.erdos_41) ↔ H1 := by
  refine ⟨finite_of_liminf, ?_⟩
  intro hfinite A hB hA
  by_contra hne
  have hnn := le_liminf_of_le (OMA.R_Erdos41_erdos_41_R1.upper_ratio A hB)
    (Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg ((A ∩ Icc 1 n).ncard))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  let f := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hA
  have hr : range f = A := Nat.range_nth_of_infinite hA
  have hpos : 0 < atTop.liminf (fun n : ℕ =>
      ((range f ∩ Icc 1 n).ncard : ℝ)/(n:ℝ)^(1/3:ℝ)) := by
    rw [hr]
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  obtain ⟨K,n₀,hk⟩ := upper_cubic hf hpos
  exact impossible_cubic_bound hfinite finite_packing hf
    ⟨K,eventually_atTop.mpr ⟨n₀,hk⟩⟩ (hr ▸ hB)

end OMA.R_Erdos41_erdos_41_R1_H2_R1
