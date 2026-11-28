import OMAStatements.S_oeis_a395111
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OMA.S_oeis_a395111

open Filter Topology

lemma square_mono (n : ℕ) : Monotone (fun L => squareWays L n) := by
  apply monotone_nat_of_le_succ
  intro L
  exact Nat.le_add_right _ _

lemma add_prime {n p : ℕ} (hp : p.Prime) : squareWays (p-1) n ≤ squareWays p (n+p) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  subst p
  simp [squareWays, hp.squarefree]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
lemma witness : A 44 = 53 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
lemma small_values : ∀ n : Fin 33, B n ≠ 53 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
lemma base_range : ∀ j : Fin 38, 54 ≤ squareWays 18 (33+j.val) := by decide +kernel

lemma many (n : ℕ) (hn : 33 ≤ n) : 54 ≤ squareWays (max 18 (n-33)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n ≤ 70
    · let j : Fin 38 := ⟨n-33, by omega⟩
      have h := base_range j
      change 54 ≤ squareWays 18 (33+(n-33)) at h
      rw [show 33+(n-33)=n by omega] at h
      exact h.trans (square_mono n (le_max_left ..))
    · obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul ((n-33)/2) (by omega)
      have h := ih (n-p) (by omega) (by omega)
      have hsmall : max 18 (n-p-33) ≤ p-1 := by omega
      have hlarge : p ≤ max 18 (n-33) := by omega
      have hh := (h.trans (square_mono _ hsmall)).trans (add_prime hp)
      rw [show n-p+p=n by omega] at hh
      exact hh.trans (square_mono _ hlarge)

theorem missing (n : ℕ) : B n ≠ 53 := by
  by_cases hn : n < 33
  · exact small_values ⟨n,hn⟩
  · have hh := (many n (by omega)).trans (square_mono n (show max 18 (n-33) ≤ n by omega))
    change 54 ≤ squareWays n n at hh
    exact Nat.ne_of_gt hh

theorem disproof : ¬ (Set.range A = Set.range B ∧
    Tendsto (fun N : ℕ => ((((Finset.range N).filter (fun n => A n = 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0)) := by
  rintro ⟨he,_⟩
  have h : 53 ∈ Set.range A := ⟨44,witness⟩
  rw [he] at h
  obtain ⟨n,h⟩ := h
  exact missing n h

open Finset
noncomputable section
open scoped Classical

lemma radical_prod {n : ℕ} (h : n ≠ 0) : rad n = ∏ p ∈ n.primeFactors, p := by
  unfold rad
  rw [if_neg h, ← Nat.toFinset_factors]
  have hh := List.prod_toFinset id (List.nodup_dedup n.primeFactorsList)
  have he : n.primeFactorsList.dedup.toFinset = n.primeFactors := by
    ext p
    simp [← Nat.toFinset_factors]
  simpa [he] using hh.symm

lemma rad_of_sf {n : ℕ} (h : Squarefree n) : rad n = n := by
  rw [radical_prod h.ne_zero, Nat.prod_primeFactors_of_squarefree h]

lemma rad_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b) :
    rad (a*b) = rad a * rad b := by
  rw [radical_prod (Nat.mul_pos ha hb).ne', radical_prod ha.ne', radical_prod hb.ne',
    Nat.primeFactors_mul ha.ne' hb.ne', prod_union hc.disjoint_primeFactors]

lemma radical_mono (n s : ℕ) : Monotone (fun L => radicalWays L n s) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Nat.le_add_right _ _

lemma radical_empty (L : ℕ) : radicalWays L 0 0 = 1 := by
  induction L with
  | zero => decide
  | succ L ih => simp [radicalWays,ih]

lemma counted_parts (L : ℕ) (P : Finset ℕ) (hp : ∀ x ∈ P, 0 < x ∧ x ≤ L) :
    1 ≤ radicalWays L (∑ x ∈ P,x) (∑ x ∈ P,rad x) := by
  induction L generalizing P with
  | zero =>
    have he : P = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by have := hp x hx; omega
    simp [he,radicalWays]
  | succ L ih =>
    by_cases he : L+1 ∈ P
    · let Q := P.erase (L+1)
      have hq : ∀ x ∈ Q, 0 < x ∧ x ≤ L := by
        intro x hx
        obtain ⟨hne,hmem⟩ := mem_erase.mp hx
        have hz := hp x hmem
        exact ⟨hz.1,by omega⟩
      have h := ih Q hq
      have hn : (∑ x ∈ Q,x)+(L+1) = ∑ x ∈ P,x := sum_erase_add _ _ he
      have hs : (∑ x ∈ Q,rad x)+rad (L+1) = ∑ x ∈ P,rad x := sum_erase_add _ _ he
      rw [radicalWays, ← hn, ← hs, if_pos ⟨by omega,by omega⟩]
      simp only [Nat.add_sub_cancel]
      omega
    · apply (ih P ?_).trans (radical_mono _ _ (Nat.le_succ L))
      intro x hx
      have hh := hp x hx
      have hn : x ≠ L+1 := fun eq => he (eq ▸ hx)
      exact ⟨hh.1,by omega⟩

lemma alternative {q m : ℕ} (hq : 0<q) (hm : Squarefree m) (hc : q.Coprime m)
    (S : Finset ℕ) (hs : ∑ x ∈ S,x = m)
    (hh : ∀ x ∈ S, 0 < x ∧ x < m ∧ Squarefree x ∧ q.Coprime x) : 2 ≤ A (q*m) := by
  let f := fun x : ℕ => q*x
  have hfi : Function.Injective f := fun x y h => Nat.eq_of_mul_eq_mul_left hq h
  let T := S.image f
  have ht : ∀ x ∈ T, 0<x ∧ x ≤ q*m-1 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have hz := hh y hy
    exact ⟨Nat.mul_pos hq hz.1, Nat.le_pred_of_lt (Nat.mul_lt_mul_of_pos_left hz.2.1 hq)⟩
  have ht1 : ∑ x ∈ T,x = q*m := by
    rw [show T=S.image f from rfl, sum_image hfi.injOn, ← hs, mul_sum]
  have ht2 : ∑ x ∈ T,rad x = rad (q*m) := by
    rw [show T=S.image f from rfl, sum_image hfi.injOn, rad_coprime hq hm.ne_zero.bot_lt hc,
      rad_of_sf hm, ← hs, mul_sum]
    apply sum_congr rfl
    intro i hi
    have h := hh i hi
    rw [show f i=q*i from rfl,rad_coprime hq h.1 h.2.2.2,rad_of_sf h.2.2.1]
  have hw := counted_parts _ _ ht
  rw [ht1,ht2] at hw
  have hpos : 0 < q*m := Nat.mul_pos hq hm.ne_zero.bot_lt
  unfold A
  generalize hx : q*m = z at *
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  simpa [radicalWays, radical_empty] using (show 2 ≤ radicalWays k (k+1) (rad (k+1))+1 by
    simp at hw; omega)

lemma shift_set (q M : ℕ) (hM : M ≠ 0) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ p ∈ S, p.Prime ∧ q < p) ∧ M ∣ ∑ p ∈ S,p := by
  have build (k : ℕ) : ∃ S : Finset ℕ, S.card=k ∧
      (∀ p ∈ S, p.Prime ∧ q<p) ∧ (∑ p ∈ S,p) ≡ k [MOD M] := by
    induction k with
    | zero => exact ⟨∅,by simp,by simp,by simp only [sum_empty]; rfl⟩
    | succ k ih =>
      obtain ⟨S,hcard,hs,hmod⟩ := ih
      obtain ⟨p,hp,hbound,hpm⟩ := Nat.exists_prime_gt_modEq_one (max q (S.sup id)) hM
      have hnot : p ∉ S := fun h => (not_lt_of_ge ((Finset.le_sup (f:=id) h).trans (le_max_right ..))) hbound
      refine ⟨insert p S, by simp [hnot,hcard], ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | h
        · exact ⟨hp, (le_max_left ..).trans_lt hbound⟩
        · exact hs _ h
      · rw [sum_insert hnot]
        simpa [Nat.add_comm] using hpm.add hmod
  obtain ⟨S,hn,hs,hmod⟩ := build M
  refine ⟨S,card_pos.mp (by omega),hs,Nat.modEq_zero_iff_dvd.mp ?_⟩
  exact hmod.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)

def tally (P : ℕ → Prop) (N : ℕ) : ℕ := ((range N).filter P).card

def negligible (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, (tally P N : ℝ) ≤ C + ε*N

lemma tally_le {P Q : ℕ → Prop} {N : ℕ} (h : ∀ n, P n → Q n) : tally P N ≤ tally Q N :=
  card_le_card (fun n hn => mem_filter.mpr ⟨(mem_filter.mp hn).1,h n (mem_filter.mp hn).2⟩)

lemma tally_union (P Q : ℕ → Prop) (N : ℕ) :
    tally (fun n => P n ∨ Q n) N ≤ tally P N + tally Q N := by
  unfold tally
  apply (card_le_card (t := ((range N).filter P) ∪ ((range N).filter Q)) ?_).trans (card_union_le ..)
  intro i hi
  simp only [mem_filter] at hi
  obtain ⟨hN,h⟩ := hi
  exact mem_union.mpr (h.imp (fun a => mem_filter.mpr ⟨hN,a⟩) (fun b => mem_filter.mpr ⟨hN,b⟩))

lemma negligible_le {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (hq : negligible Q) :
    negligible P := by
  intro ε hε
  obtain ⟨C,hC⟩ := hq ε hε
  exact ⟨C,fun N => (Nat.cast_le.mpr (tally_le h)).trans (hC N)⟩

lemma negligible_union {P Q : ℕ → Prop} (hp : negligible P) (hq : negligible Q) :
    negligible (fun n => P n ∨ Q n) := by
  intro ε hε
  obtain ⟨C,hC⟩ := hp (ε/2) (half_pos hε)
  obtain ⟨D,hD⟩ := hq (ε/2) (half_pos hε)
  refine ⟨C+D,?_⟩
  intro N
  have hh : (tally (fun n => P n ∨ Q n) N:ℝ) ≤ (tally P N:ℝ)+tally Q N := by
    exact_mod_cast tally_union P Q N
  linarith only [hh,hC N,hD N]

lemma negligible_finite {P : ℕ → ℕ → Prop} (S : Finset ℕ)
    (h : ∀ i ∈ S, negligible (P i)) : negligible (fun n => ∃ i ∈ S, P i n) := by
  induction S using Finset.induction_on with
  | empty =>
    intro ε hε
    exact ⟨0, fun N => by simp [tally]; positivity⟩
  | @insert a s ha ih =>
    apply negligible_le (Q := fun n => P a n ∨ ∃ i ∈ s, P i n)
    · simp
    · exact negligible_union (h a (mem_insert_self ..)) (ih fun i hi => h _ (mem_insert_of_mem hi))

lemma tally_inject {P Q : ℕ → Prop} (f : ℕ → ℕ) (N : ℕ)
    (hm : ∀ n, P n → Q (f n)) (hl : ∀ n, P n → f n ≤ n)
    (hinj : ∀ i j, P i → P j → f i = f j → i = j) : tally P N ≤ tally Q N := by
  apply card_le_card_of_injOn f
  · intro n hn
    obtain ⟨hN,hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr ((hl _ hp).trans_lt (mem_range.mp hN)),hm _ hp⟩
  · intro i hi j hj eq
    exact hinj _ _ (mem_filter.mp hi).2 (mem_filter.mp hj).2 eq

lemma negligible_scaled {q : ℕ} (hq : 0<q) {P : ℕ → Prop} (hp : negligible P) :
    negligible (fun n => ∃ m, n=q*m ∧ P m) := by
  intro ε hε
  obtain ⟨C,hC⟩ := hp ε hε
  refine ⟨C,fun N => (Nat.cast_le.mpr ?_).trans (hC N)⟩
  apply tally_inject (fun n => n/q)
  · rintro n ⟨m,rfl,hm⟩
    simpa [Nat.mul_div_cancel_left _ hq] using hm
  · intro n _; exact Nat.div_le_self .. 
  · rintro i j ⟨u,rfl,_⟩ ⟨v,rfl,_⟩ hh
    simpa [Nat.mul_div_cancel_left _ hq] using congrArg (q*·) hh

def bigSquare (K n : ℕ) : Prop := 0<n ∧ ∃ d, K<d ∧ d^2 ∣ n

lemma telescopes (K L : ℕ) (hK : 0<K) :
    (∑ t ∈ range L, (1:ℝ)/((K:ℝ)+t+1)^2) ≤ 1/K - 1/((K:ℝ)+L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ]
    push_cast
    have hx : 0 < (K:ℝ)+L := by positivity
    have hz : (1:ℝ)/((K:ℝ)+L+1)^2 ≤ 1/((K:ℝ)+L) - 1/((K:ℝ)+L+1) := by
      field_simp
      nlinarith only [hx]
    rw [← add_assoc (K:ℝ) (L:ℝ) 1]
    linarith only [hz,ih]

lemma square_tail (K N : ℕ) (hK : 0<K) : (tally (bigSquare K) N : ℝ) ≤ N/K := by
  let U := fun t : ℕ => (range (N+1)).filter fun n => n ≠ 0 ∧ (K+t+1)^2 ∣ n
  have hsub : (range N).filter (bigSquare K) ⊆ (range N).biUnion U := by
    intro n hn
    obtain ⟨hN,hpos,d,hd,hdiv⟩ := mem_filter.mp hn
    have hx := Nat.le_of_dvd hpos hdiv
    have hd' : d ≤ d^2 := Nat.le_self_pow (by decide) d
    have ht := mem_range.mp hN
    refine mem_biUnion.mpr ⟨d-(K+1),mem_range.mpr (by omega),?_⟩
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by omega),hpos.ne',by simpa [show K+(d-(K+1))+1=d by omega] using hdiv⟩
  have hcard : tally (bigSquare K) N ≤ ∑ t ∈ range N,N/(K+t+1)^2 :=
    (card_le_card hsub).trans (card_biUnion_le.trans_eq (sum_congr rfl fun t _ => Nat.card_multiples' ..))
  calc
    _ ≤ ∑ t ∈ range N, ((N/(K+t+1)^2:ℕ):ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ t ∈ range N, (N:ℝ) * (1/((K:ℝ)+t+1)^2) := by
      apply sum_le_sum
      intro t _
      have h := Nat.div_mul_le_self N ((K+t+1)^2)
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).2
      exact_mod_cast h
    _ ≤ _ := by
      rw [← mul_sum,div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hz : 0 ≤ (1:ℝ)/((K:ℝ)+N) := by positivity
      simpa [one_div] using (telescopes K N hK).trans (sub_le_self _ hz)

def isolated (q m : ℕ) : Prop := Squarefree m ∧ q.Coprime m ∧ A (q*m)=1

lemma good_remainder (q K : ℕ) (hq : 0<q) :
    ∃ s : ℕ, ∀ m : ℕ, 2*s<m → isolated q m → bigSquare K (m-s) := by
  let M := q*(K.factorial)^2
  obtain ⟨S,hne,hs,hdiv⟩ := shift_set q M (Nat.mul_pos hq (pow_pos (Nat.factorial_pos _) _)).ne'
  let s := ∑ p ∈ S,p
  have hpos : 0<s := sum_pos (fun p hp => (hs p hp).1.pos) hne
  have hqdiv : q ∣ s := (dvd_mul_right q _).trans hdiv
  refine ⟨s,?_⟩
  intro m hbig hi
  obtain ⟨hm,hcm,hA⟩ := hi
  have hsm : s ≤ m := by omega
  have hsum : s+(m-s)=m := by omega
  have hsmall (p) (hp : p ∈ S) : p ≤ s := single_le_sum (fun i _ => Nat.zero_le i) hp
  have hcop : q.Coprime (m-s) := by
    obtain ⟨v,hv⟩ := hqdiv
    apply (Nat.coprime_mul_left_add_right q (m-s) v).mp
    rwa [← hv,hsum]
  have hnonsq : ¬ Squarefree (m-s) := by
    intro hsf
    have hnot : m-s ∉ S := fun h => by have := hsmall _ h; omega
    have ha := alternative hq hm hcm (insert (m-s) S)
      (by rw [sum_insert hnot]; change m-s+s=m; omega) (by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact ⟨by omega, by omega, hsf, hcop⟩
        · have hp := hs x hx
          exact ⟨hp.1.pos,(hsmall _ hx).trans_lt (by omega),hp.1.squarefree,
            (hp.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq hp.2)).symm⟩)
    omega
  rw [Nat.squarefree_iff_prime_squarefree] at hnonsq
  push Not at hnonsq
  obtain ⟨p,hp,hpd⟩ := hnonsq
  refine ⟨by omega,p,?_,by simpa [pow_two] using hpd⟩
  by_contra! hle
  have hf := Nat.dvd_factorial hp.pos hle
  have hd : p*p ∣ s := (show p*p ∣ M from (mul_dvd_mul hf hf).trans
    (by rw [show M=q*(K.factorial*K.factorial) by simp [M,pow_two]]; exact dvd_mul_left ..)).trans hdiv
  exact (Nat.squarefree_iff_prime_squarefree.mp hm p hp) (hsum ▸ dvd_add hd hpd)

lemma choose_cut {ε : ℝ} (hε : 0<ε) : ∃ K : ℕ, 0<K ∧ 1/(K:ℝ) ≤ ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε)
  have hpos : (0:ℝ) < K := (one_div_pos.mpr hε).trans hK
  refine ⟨K, by exact_mod_cast hpos, (div_le_iff₀ hpos).mpr ?_⟩
  have hh := (div_lt_iff₀ hε).mp hK
  linarith

lemma fixed_negligible {q : ℕ} (hq : 0<q) : negligible (isolated q) := by
  intro ε hε
  obtain ⟨K,hK,hcut⟩ := choose_cut hε
  obtain ⟨s,hs⟩ := good_remainder q K hq
  let F := fun n : ℕ => n ≤ 2*s
  let G := fun n : ℕ => 2*s<n ∧ isolated q n
  refine ⟨(2*s+1:ℕ),?_⟩
  intro N
  have hf : tally F N ≤ 2*s+1 := by
    apply (card_le_card (t := range (2*s+1)) ?_).trans_eq (card_range _)
    intro i hi
    simp only [mem_filter] at hi
    exact mem_range.mpr (Nat.lt_succ_of_le hi.2)
  have hg : tally G N ≤ tally (bigSquare K) N := by
    apply tally_inject (fun n => n-s)
    · exact fun n h => hs n h.1 h.2
    · exact fun _ _ => Nat.sub_le .. 
    · rintro i j ⟨hi,_⟩ ⟨hj,_⟩ h
      omega
  have hu := tally_le (Q := fun n => F n ∨ G n) (fun n (h : isolated q n) => by
    by_cases hi : n ≤ 2*s
    · exact Or.inl hi
    · exact Or.inr ⟨by omega,h⟩) (N := N)
  have hh := hu.trans ((tally_union F G N).trans (Nat.add_le_add hf hg))
  have he : (tally (isolated q) N : ℝ) ≤ ((2*s+1:ℕ):ℝ) + tally (bigSquare K) N := by
    exact_mod_cast hh
  have hr := square_tail K N hK
  have hmul := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg N)
  rw [one_div, ← div_eq_inv_mul] at hmul
  linarith

lemma split_number {n L : ℕ} (hn : 0<n) (h : ¬ bigSquare L n) :
    ∃ q m : ℕ, 0<q ∧ q≤L^3 ∧ n=q*m ∧ Squarefree m ∧ q.Coprime m := by
  obtain ⟨b,d,hb,hd,he,hs⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hdl : d ≤ L := by
    by_contra! hgt
    exact h ⟨hn,d,hgt,he ▸ dvd_mul_right _ _⟩
  let g := b.gcd d
  let m := b/g
  have hg0 : 0<g := Nat.gcd_pos_of_pos_right _ hd
  have hgd : g ∣ d := Nat.gcd_dvd_right .. 
  have hgb : g ∣ b := Nat.gcd_dvd_left .. 
  have hgm : m*g=b := Nat.div_mul_cancel hgb
  have hs' : Squarefree (m*g) := hgm ▸ hs
  have hmd : m.Coprime d := Nat.coprime_div_gcd_of_squarefree hs hd.ne'
  refine ⟨d^2*g,m,Nat.mul_pos (pow_pos hd _) hg0,?_,?_,hs'.of_mul_left,?_⟩
  · calc d^2*g ≤ L^2*L := Nat.mul_le_mul (Nat.pow_le_pow_left hdl _) ((Nat.le_of_dvd hd hgd).trans hdl)
         _ = _ := by ring
  · rw [← he, ← hgm]
    ring
  · exact ((hmd.pow_right 2).mul_right (Nat.coprime_of_squarefree_mul hs')).symm

lemma unique_negligible : negligible (fun n => A n=1) := by
  intro ε hε
  obtain ⟨K,hK,hcut⟩ := choose_cut (half_pos hε)
  let F := fun q n : ℕ => 0<q ∧ ∃ m, n=q*m ∧ isolated q m
  have hfin : negligible (fun n => ∃ q ∈ range (K^3+1), F q n) := by
    apply negligible_finite
    intro q _
    by_cases hq : 0<q
    · exact negligible_le (fun _ h => h.2) (negligible_scaled hq (fixed_negligible hq))
    · intro δ hδ
      exact ⟨0,fun N => by simp [tally,F,hq]; positivity⟩
  obtain ⟨C,hC⟩ := hfin (ε/2) (half_pos hε)
  let Q := fun n => ∃ q ∈ range (K^3+1), F q n
  have cover (n : ℕ) (hn : A n=1) : n=0 ∨ bigSquare K n ∨ Q n := by
    rcases n.eq_zero_or_pos with h0 | h0
    · exact Or.inl h0
    by_cases h : bigSquare K n
    · exact Or.inr (Or.inl h)
    obtain ⟨q,m,hq,hl,he,hs,hcop⟩ := split_number h0 h
    exact Or.inr (Or.inr ⟨q,mem_range.mpr (by omega),hq,m,he,hs,hcop,he ▸ hn⟩)
  refine ⟨1+C,?_⟩
  intro N
  have hzero : tally (fun n => n=0) N ≤ 1 := by
    apply (card_le_card (t := {0}) ?_).trans_eq (card_singleton _)
    intro i hi
    simp only [mem_filter] at hi
    exact mem_singleton.mpr hi.2
  have hu := (tally_le (N:=N) cover).trans ((tally_union _ _ _).trans
    (Nat.add_le_add hzero (tally_union _ _ _)))
  have hh : (tally (fun n => A n=1) N:ℝ) ≤ 1+(tally (bigSquare K) N:ℝ)+tally Q N := by
    exact_mod_cast (Nat.add_assoc .. ▸ hu)
  have hmul := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg N)
  rw [one_div, ← div_eq_inv_mul] at hmul
  linarith only [hh,square_tail K N hK,hmul,hC N]

theorem density_zero :
    Tendsto (fun N : ℕ => ((((range N).filter (fun n => A n=1)).card:ℕ):ℝ)/N) atTop (𝓝 0) := by
  have hid (N : ℕ) : ((range N).filter (fun n => A n=1)).card = tally (fun n => A n=1) N := by
    unfold tally
    apply congrArg Finset.card
    ext i
    simp only [mem_filter]
  simp_rw [hid]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C,hC⟩ := unique_negligible (ε/2) (half_pos hε)
  have hh := (tendsto_const_div_atTop_nhds_zero_nat (𝕜:=ℝ) C).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hh,eventually_ge_atTop 1] with N hc hN
  change C/(N:ℝ) < ε/2 at hc
  have hpos : 0<(N:ℝ) := by exact_mod_cast hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  apply (div_lt_iff₀ hpos).mpr
  linarith only [hC N,(div_lt_iff₀ hpos).mp hc]

end

open Finset
noncomputable section
open scoped Classical

def partitions (P : ℕ → Prop) (w : ℕ → ℕ) (L n s : ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 L).powerset).filter fun A =>
    (∀ q ∈ A, P q) ∧ (∑ q ∈ A,q)=n ∧ (∑ q ∈ A,w q)=s

lemma partition_mem {P : ℕ→Prop} {w : ℕ→ℕ} {L n s : ℕ} {A : Finset ℕ} :
    A∈partitions P w L n s ↔ (∀ q ∈ A, 0<q ∧ q≤L ∧ P q) ∧
    (∑ q ∈ A,q)=n ∧ (∑ q ∈ A,w q)=s := by
  simp only [partitions,mem_filter,mem_powerset,subset_iff,mem_Icc]
  constructor
  · rintro ⟨ha,hp,hv,hw⟩
    exact ⟨fun q h => ⟨(ha h).1,(ha h).2,hp _ h⟩,hv,hw⟩
  · rintro ⟨ha,hv,hw⟩
    exact ⟨fun _ h => ⟨(ha _ h).1,(ha _ h).2.1⟩,fun _ h => (ha _ h).2.2,hv,hw⟩

lemma partition_recur (P : ℕ→Prop) (w : ℕ→ℕ) (L n s : ℕ) :
    (partitions P w (L+1) n s).card = (partitions P w L n s).card +
      if P (L+1) ∧ L+1≤n ∧ w (L+1)≤s then (partitions P w L (n-(L+1)) (s-w (L+1))).card else 0 := by
  let Q := partitions P w L (n-(L+1)) (s-w (L+1))
  let k := L+1
  have hout {nn ss : ℕ} {A : Finset ℕ} (h : A∈partitions P w L nn ss) : k∉A := by
    intro hk
    have hh := (partition_mem.mp h).1 k hk
    dsimp [k] at hh
    omega
  let ok := P k ∧ k≤n ∧ w k≤s
  let added := Q.image (insert k)
  have hsplit : partitions P w (L+1) n s = partitions P w L n s ∪ (if ok then added else ∅) := by
    ext A
    constructor
    · intro h
      obtain ⟨hA,hv,hw⟩ := partition_mem.mp h
      by_cases hk : k∈A
      · have hVk := (sum_erase_add A (fun q : ℕ => q) hk)
        have hWk := (sum_erase_add A w hk)
        have hP := (hA k hk).2.2
        have hOK : ok := ⟨hP,by omega,by omega⟩
        apply mem_union.mpr
        right
        rw [if_pos hOK]
        refine mem_image.mpr ⟨A.erase k,partition_mem.mpr ⟨?_,?_,?_⟩,insert_erase hk⟩
        · intro q hq
          obtain ⟨hne,hmem⟩ := mem_erase.mp hq
          obtain ⟨h1,h2,h3⟩ := hA q hmem
          dsimp [k] at hne
          exact ⟨h1,by omega,h3⟩
        · change _ = n-k
          omega
        · change _ = s-w k
          omega
      · apply mem_union_left
        apply partition_mem.mpr
        refine ⟨?_,hv,hw⟩
        intro q hq
        obtain ⟨h1,h2,h3⟩ := hA q hq
        have hne : q ≠ L+1 := by intro hh;subst q;exact hk hq
        exact ⟨h1,by omega,h3⟩
    · intro h
      rcases mem_union.mp h with h|h
      · obtain ⟨hp,hv,hw⟩ := partition_mem.mp h
        exact partition_mem.mpr ⟨fun q hq => ⟨(hp q hq).1,Nat.le_succ_of_le (hp q hq).2.1,
          (hp q hq).2.2⟩,hv,hw⟩
      · split at h
        next hOK =>
          obtain ⟨B,hB,rfl⟩ := mem_image.mp h
          obtain ⟨hb,hv,hw⟩ := partition_mem.mp hB
          obtain ⟨hpp,hnn,hss⟩ := hOK
          apply partition_mem.mpr
          change (∑ q ∈ B,q)=n-k at hv
          change (∑ q ∈ B,w q)=s-w k at hw
          simp only [sum_insert (hout hB)]
          refine ⟨?_,by omega,by omega⟩
          intro q hq
          rcases mem_insert.mp hq with rfl|h'
          · exact ⟨Nat.succ_pos _,le_rfl,hpp⟩
          · exact ⟨(hb _ h').1,Nat.le_succ_of_le (hb _ h').2.1,(hb _ h').2.2⟩
        next => simp at h
  have hdis : Disjoint (partitions P w L n s) added := by
    apply disjoint_left.mpr
    intro A hA hh
    obtain ⟨B,_,he⟩ := mem_image.mp hh
    exact hout hA (he ▸ mem_insert_self k B)
  rw [hsplit]
  by_cases hok : ok
  · rw [if_pos hok,if_pos hok,card_union_of_disjoint hdis]
    congr 1
    apply card_image_of_injOn
    intro A hA B hB he
    have h := congrArg (fun C : Finset ℕ => C.erase k) he
    simpa [erase_insert (hout hA),erase_insert (hout hB)] using h
  · rw [if_neg hok,if_neg hok,union_empty,add_zero]

theorem radicalWays_card (L n s : ℕ) :
    radicalWays L n s = (partitions (fun _ => True) rad L n s).card := by
  induction L generalizing n s with
  | zero =>
    by_cases hn : n=0 <;> by_cases hs : s=0 <;> simp [partitions,radicalWays,Finset.filter_singleton,hn,hs,eq_comm]
  | succ L ih => simp only [radicalWays,partition_recur,true_and,ih]

theorem squareWays_card (L n : ℕ) :
    squareWays L n = (partitions Squarefree (fun _ => 0) L n 0).card := by
  induction L generalizing n with
  | zero =>
    by_cases hn : n=0 <;> simp [partitions,squareWays,Finset.filter_singleton,hn,eq_comm]
  | succ L ih =>
    simp only [squareWays,partition_recur,le_refl,and_true,Nat.sub_zero,ih]

theorem original_partition_results :
    ((partitions (fun _ => True) rad 44 44 (rad 44)).card = 53 ∧
      ∀ n, (partitions Squarefree (fun _ => 0) n n 0).card ≠ 53) ∧
    Tendsto (fun N : ℕ => ((((Finset.range N).filter (fun n =>
      (partitions (fun _ => True) rad n n (rad n)).card = 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
  simp only [← radicalWays_card,← squareWays_card]
  exact ⟨⟨witness,missing⟩,density_zero⟩

end

end OMA.S_oeis_a395111

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395111.main) :=
  OMA.S_oeis_a395111.disproof
