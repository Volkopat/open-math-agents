import FormalConjectures.GreensOpenProblems.«19»
import Mathlib

/-!
The popular-corners exponent is four, by Fox, Sah, Sawhney, Stoner, and Zhao.
Based on @steveDOTdigital's reduction (PR #3878), @ppleskov's transfer
to popular corners (PR #11371), and @marcusbuffett's bound (PR #4879).
-/

section

/-! # Popular corners and triforce densities

The finite triforce lower bound follows by discarding low-codegree pairs. For the converse, locally linear graphs from the Ruzsa–Szemerédi construction yield densities close to the reciprocal of their number of vertices. The two transfer statements translate between finite templates and popular corners. See Mandache, A variant of the Corners theorem (2021), and Fox, Sah, Sawhney, Stoner and Zhao, Triforce and corners (2020). -/

namespace OMA.R_Green19_green_19_R1


open Finset Filter Real Topology
open scoped Classical
lemma small_fibers {E X : Type*} [DecidableEq X] [Fintype X]
    (H : Finset E) (proj : E → X) (s : ℝ) (hs : 0 ≤ s) :
    let deg (x : X) : ℝ := (H.filter (fun z => proj z = x)).card
    ((H.filter (fun e => deg (proj e) < s)).card : ℝ) ≤ Fintype.card X*s := by
  intro deg
  classical
  let B := H.filter (fun e => deg (proj e) < s)
  have eq := Finset.card_eq_sum_card_fiberwise (s:=B) (t:=(univ : Finset X)) (f:=proj) (fun _ _ => mem_univ _)
  have r (x : X) : ((B.filter (fun e => proj e=x)).card:ℝ) ≤ s := by
    by_cases sm : deg x < s
    · refine le_trans ?_ sm.le
      unfold deg
      exact_mod_cast Finset.card_le_card (filter_subset_filter _ (filter_subset _ _))
    · have empty : B.filter (fun e => proj e = x) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e h
        obtain ⟨he,hx⟩ := mem_filter.mp h
        exact sm (hx ▸ (mem_filter.mp he).2)
      simp only [empty,card_empty,Nat.cast_zero]; exact hs
  change (B.card:ℝ) ≤ _
  calc
    _ = ∑ x : X, ((B.filter (fun e => proj e=x)).card:ℝ) := by exact_mod_cast eq
    _ ≤ ∑ _x : X,s := sum_le_sum (fun x _ => r x)
    _ = _ := by simp

lemma triforce_lower {q : ℕ} (hq : 0<q) (H : Finset (Fin q × Fin q × Fin q)) :
    let xy (e : Fin q × Fin q × Fin q) := (e.1,e.2.1)
    let xz (e : Fin q × Fin q × Fin q) := (e.1,e.2.2)
    let yz (e : Fin q × Fin q × Fin q) := (e.2.1,e.2.2)
    let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
      (H.filter (fun e => proj e = x)).card
    let density : ℝ := H.card / (q:ℝ)^3
    let triforce := (∑ e : Fin q × Fin q × Fin q,
      deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q:ℝ)^6
    (1/432:ℝ) * density ^ (4:ℕ) ≤ triforce := by
  intro xy xz yz deg density triforce
  classical
  let t : ℝ := H.card
  let s : ℝ := t/(6*q^2)
  have qp : 0 < (q:ℝ) := by exact_mod_cast hq
  have hn : 0 ≤ t := Nat.cast_nonneg _
  have sn : 0 ≤ s := by dsimp [s]; positivity
  let bad (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) := H.filter (fun e => deg proj (proj e) < s)
  let B := (bad xy ∪ bad xz) ∪ bad yz
  let G := H \ B
  have few (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) : ((bad proj).card:ℝ) ≤ t / 6 := by
    have h := small_fibers H proj s sn
    rw [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at h
    have cancel : (q:ℝ)*q*s = t/6 := by dsimp [s]; field_simp
    exact h.trans_eq cancel
  have b : (B.card:ℝ) ≤ t/2 := by
    have h : B.card ≤ (bad xy).card + (bad xz).card + (bad yz).card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have hr : (B.card:ℝ) ≤ (bad xy).card + ((bad xz).card:ℝ) + (bad yz).card := by exact_mod_cast h
    linarith [few xy,few xz,few yz]
  have cover : H ⊆ G ∪ B := by intro e he; by_cases h : e ∈ B <;> simp [G,h,he]
  have sz : (H.card:ℝ) ≤ (G.card:ℝ) + B.card := by exact_mod_cast (card_le_card cover).trans (card_union_le _ _)
  have lg : t/2 ≤ (G.card:ℝ) := by change t ≤ _ at sz; linarith
  let val (e : (Fin q × Fin q × Fin q)) := deg xy (xy e) * deg xz (xz e) * deg yz (yz e)
  have good (e : (Fin q × Fin q × Fin q)) (he : e ∈ G) : s^3 ≤ val e := by
    obtain ⟨hit,out⟩ := mem_sdiff.mp he
    have ok (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (inc : bad proj ⊆ B) : s ≤ deg proj (proj e) :=
      le_of_not_gt (fun lt => out (inc (mem_filter.mpr ⟨hit,lt⟩)))
    have a := ok xy (fun _ h => mem_union_left _ (mem_union_left _ h))
    have b := ok xz (fun _ h => mem_union_left _ (mem_union_right _ h))
    have c := ok yz (fun _ h => mem_union_right _ h)
    dsimp [val]
    rw [pow_succ,sq]
    exact mul_le_mul (mul_le_mul a b sn (sn.trans a)) c sn (mul_nonneg (sn.trans a) (sn.trans b))
  have vnon (e : (Fin q × Fin q × Fin q)) : 0 ≤ val e := by dsimp [val,deg]; positivity
  have total : (t/2)*s^3 ≤ ∑ e : (Fin q × Fin q × Fin q), val e := calc
    _ ≤ (G.card:ℝ)*s^3 := mul_le_mul_of_nonneg_right lg (pow_nonneg sn _)
    _ = ∑ _e ∈ G,s^3 := by simp
    _ ≤ ∑ e ∈ G,val e := sum_le_sum good
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun e _ _ => vnon e)
  change (1/432:ℝ)*(t/q^3)^4 ≤ (∑ e : (Fin q × Fin q × Fin q),val e)/q^6
  rw [le_div_iff₀ (pow_pos qp 6)]
  apply le_trans (le_of_eq ?_) total
  dsimp [s]
  field_simp
  ring


-- Convex power-law lower bounds for finite triforce models transfer to popular corners.
def H1 : Prop := ∀ c : ℝ, 1 ≤ c → ∀ b > (0:ℝ),
    (∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
    let xy (e : Fin q × Fin q × Fin q) := (e.1,e.2.1)
    let xz (e : Fin q × Fin q × Fin q) := (e.1,e.2.2)
    let yz (e : Fin q × Fin q × Fin q) := (e.2.1,e.2.2)
    let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
      (H.filter (fun e => proj e = x)).card
    let density : ℝ := H.card / (q:ℝ)^3
    let triforce := (∑ e : Fin q × Fin q × Fin q,
      deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q:ℝ)^6
    b * density^c ≤ triforce) →
    Green19.ValidExponent c

-- Sampling the triangle hypergraph of a locally linear graph yields sets with few
-- corners simultaneously in every nonzero direction, in arbitrarily high dimensions.
def H2 : Prop := ∀ q : ℕ, 1 < q → ∀ (G : SimpleGraph (Fin q)) [DecidableRel G.Adj], G.LocallyLinear →
    ∃ᶠ n : ℕ in atTop, ∃ A : Finset (𝔽₂ n × 𝔽₂ n),
      let N : ℝ := Fintype.card (𝔽₂ n)
      ((G.cliqueFinset 3).card:ℝ) / (q:ℝ)^3 * N^2 ≤ A.card ∧
        ∀ d : 𝔽₂ n, d ≠ 0 → ((Green19.S d A).card:ℝ) ≤ (2/(q:ℝ)^4) * N^2



open Finset Filter Real Asymptotics Topology
lemma many_triangles (η : ℝ) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, (q:ℝ)^((2:ℝ)-η) ≤ (ruzsaSzemerediNumberNat q : ℝ) := by
  obtain ⟨C,hC,bound⟩ := ruzsaSzemerediNumberNat_asymptotic_lower_bound.exists_pos
  have logs := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [bound.bound,logs.eventually_ge_atTop ((8/η)^2),
    logs.eventually_ge_atTop (2*log C/η),eventually_gt_atTop 1] with q b sq big hq
  have qp : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  let l := log (q:ℝ)
  change (8/η)^2 ≤ l at sq
  change 2*log C/η ≤ l at big
  have nl : 0 ≤ l := (sq_nonneg _).trans sq
  have root : 8/η ≤ √l := (le_sqrt (by positivity) nl).mpr sq
  have re := (div_le_iff₀ hη).mp root
  have bb := (div_le_iff₀ hη).mp big
  have re' := mul_le_mul_of_nonneg_right re (sqrt_nonneg l)
  have sr : √l*η*√l = l*η := calc
    _ = (√l)^2*η := by ring
    _ = _ := by rw [Real.sq_sqrt nl]
  rw [sr] at re'
  have sm : log C + 4*√l ≤ l*η := by linarith
  have lhs : C*(q:ℝ)^((2:ℝ)-η) ≤ (q:ℝ)^2 * exp (-4*√l) := by
    rw [← Real.rpow_natCast (q:ℝ) 2]
    simp only [Real.rpow_def_of_pos qp]
    rw [← Real.exp_log hC,← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
    change log C + l*(2-η) ≤ l*2 + -4*√l
    linarith
  have rhs : (q:ℝ)^2*exp (-4*√l) ≤ C*(ruzsaSzemerediNumberNat q:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (exp_pos _).le),
      abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (ruzsaSzemerediNumberNat q))] using b
  exact (mul_le_mul_iff_right₀ hC).mp (lhs.trans rhs)


lemma graph_test (transfer : H2) {q : ℕ} (hq : 1<q) {α b K : ℝ}
    (dens : α ≤ (ruzsaSzemerediNumberNat q:ℝ)/(q:ℝ)^3)
    (popular : ∀ᶠ n : ℕ in atTop, ∀ A : Finset (𝔽₂ n × 𝔽₂ n),
      let N : ℝ := Fintype.card (𝔽₂ n)
      α*N^2 ≤ A.card → ∃ d : 𝔽₂ n, d ≠ 0 ∧ K*α^b*N^2 ≤ (Green19.S d A).card) :
    K*α^b ≤ 2/(q:ℝ)^4 := by
  obtain ⟨G,adj,card,linear⟩ := ruzsaSzemerediNumber_spec (α:=Fin q)
  let _ : DecidableRel G.Adj := adj
  have dup : (G.cliqueFinset 3).card = ruzsaSzemerediNumberNat q := card
  obtain ⟨n,found,every⟩ := ((transfer q hq G linear).and_eventually popular).exists
  obtain ⟨A,lo,hi⟩ := found
  let N : ℝ := Fintype.card (𝔽₂ n)
  have Np : 0 < N := by dsimp only [N]; exact_mod_cast (Fintype.card_pos (α:=𝔽₂ n))
  have val : α ≤ ((G.cliqueFinset 3).card:ℝ)/(q:ℝ)^3 := by rw [dup]; exact dens
  have lo' : ((G.cliqueFinset 3).card:ℝ)/(q:ℝ)^3*N^2 ≤ A.card := lo
  have inA : α*N^2 ≤ A.card := (mul_le_mul_of_nonneg_right val (sq_nonneg N)).trans lo'
  obtain ⟨d,ne,yes⟩ := every A inA
  exact (mul_le_mul_iff_left₀ (pow_pos Np 2)).mp (yes.trans (hi d ne))

lemma exponent_mono {c b : ℝ} (cb : c ≤ b) (hc : Green19.ValidExponent c) :
    Green19.ValidExponent b := by
  obtain ⟨K,hK,valid⟩ := hc
  refine ⟨K,hK,?_⟩
  intro α pos lt
  filter_upwards [valid α pos lt] with n hn
  intro A
  dsimp only
  intro dens
  obtain ⟨d,hd,low⟩ := hn A dens
  refine ⟨d,hd,le_trans ?_ low⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge pos lt.le cb) hK.le) (sq_nonneg _)

lemma exponent_obstruction (transfer : H2) {b : ℝ} (hb : 1 ≤ b)
    (valid : Green19.ValidExponent b) : 4 ≤ b := by
  by_contra! small
  obtain ⟨K,hK,v⟩ := valid
  let η := (4-b)/(2*b)
  have bp : 0 < b := by linarith
  have ηp : 0 < η := div_pos (by linarith) (by positivity)
  let a := 1+η
  have ap : 0 < a := by dsimp [a]; positivity
  have ab : a*b = (4+b)/2 := by dsimp [a,η]; field_simp; ring
  have gap : 0 < 4-a*b := by linarith
  have grows := (tendsto_rpow_atTop gap).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨q,many,large,hq⟩ := ((many_triangles η ηp).and
    ((grows.eventually_gt_atTop (2/K)).and (eventually_gt_atTop 1))).exists
  have qp : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have q1 : 1<(q:ℝ) := by exact_mod_cast hq
  let α := (q:ℝ)^(-a)
  have αp : 0 < α := Real.rpow_pos_of_pos qp _
  have α1 : α < 1 := Real.rpow_lt_one_of_one_lt_of_neg q1 (neg_lt_zero.mpr ap)
  have dens : α ≤ (ruzsaSzemerediNumberNat q:ℝ)/(q:ℝ)^3 := by
    rw [le_div_iff₀ (pow_pos qp 3)]
    apply le_trans (le_of_eq ?_) many
    dsimp [α]
    rw [← Real.rpow_natCast (q:ℝ) 3,← Real.rpow_add qp]
    congr 1
    dsimp [a]
    ring
  have limited : K*α^b ≤ 2/(q:ℝ)^4 := graph_test transfer hq dens (v α αp α1)
  have impossible := (le_div_iff₀ (pow_pos qp 4)).mp limited
  have scale : α^b*(q:ℝ)^4 = (q:ℝ)^(4-a*b) := by
    dsimp [α]
    rw [← Real.rpow_mul qp.le,← Real.rpow_natCast (q:ℝ) 4,← Real.rpow_add qp]
    congr 1
    ring
  rw [mul_assoc,scale] at impossible
  change 2/K < (q:ℝ)^(4-a*b) at large
  linarith [(div_lt_iff₀ hK).mp large]

theorem main : H1 → H2 → type_of% @Green19.green_19 := by
  intro transferUpper transferLower
  have v4 : Green19.ValidExponent 4 := by
    apply transferUpper 4 (by norm_num) (1/432) (by norm_num)
    intro q hq H
    simpa only [Real.rpow_ofNat] using triforce_lower hq H
  have lower {c : ℝ} (hc : Green19.ValidExponent c) : 4 ≤ c := by
    by_contra! lt
    let b := max 1 c
    have sm : b < 4 := max_lt (by norm_num) lt
    exact (not_le.mpr sm) (exponent_obstruction transferLower (le_max_left _ _) (exponent_mono (le_max_right _ _) hc))
  change sInf {c : ℝ | Green19.ValidExponent c} = 4
  exact le_antisymm (csInf_le ⟨4,fun _ h => lower h⟩ v4) (le_csInf ⟨4,v4⟩ (fun _ h => lower h))


end OMA.R_Green19_green_19_R1

end


section

/-!
# Proof of `Green19.green_19.R1.H1`

Transfers convex power-law lower bounds for finite triforce models to popular corners in
`𝔽₂ n × 𝔽₂ n`, following the regularity method of Mandache (2021) with an elementary
weighted-to-unweighted blow-up transfer and finite Fourier analysis on `𝔽₂ n`.

Credits for upstream reduction `Green19.green_19.R1`: `@steveDOTdigital` (PR #3878).
-/

open Finset Real Filter Topology
open scoped Classical

namespace Green19H1

/- ## Section 1: Weighted-to-unweighted triforce transfer -/

section WeightedTriforce

/-- Counting residues `< k` under a shift in `Fin R`. -/
private lemma card_fin_shift_lt (R : ℕ) [NeZero R] (s : Fin R) (k : ℕ) (hk : k ≤ R) :
    (univ.filter (fun c : Fin R => (s + c).val < k)).card = k := by
  have hbij : (univ.filter (fun c : Fin R => (s + c).val < k)).card =
      (univ.filter (fun r : Fin R => r.val < k)).card := by
    refine Finset.card_bij (fun c _ => s + c) ?_ ?_ ?_
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact hc
    · intro c₁ _ c₂ _ h
      exact add_left_cancel h
    · intro r hr
      refine ⟨r - s, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      simpa using hr
  rw [hbij]
  have h2 : (univ.filter (fun r : Fin R => r.val < k)).card = (Finset.range k).card := by
    refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
    · intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      exact Finset.mem_range.mpr hr
    · intro r₁ _ r₂ _ h
      exact Fin.ext h
    · intro m hm
      rw [Finset.mem_range] at hm
      refine ⟨⟨m, lt_of_lt_of_le hm hk⟩, ?_, rfl⟩
      simp [hm]
  rw [h2, Finset.card_range]

/-- Unweighted triforce lower bound transfers to `[0, 1]`-valued weights on any nonempty finite set. -/
private lemma weighted_triforce_bound
    {c b : ℝ} (hc : 1 ≤ c) (hb : 0 < b)
    (hH : ∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
      let xy (e : Fin q × Fin q × Fin q) := (e.1, e.2.1)
      let xz (e : Fin q × Fin q × Fin q) := (e.1, e.2.2)
      let yz (e : Fin q × Fin q × Fin q) := (e.2.1, e.2.2)
      let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
        (H.filter (fun e => proj e = x)).card
      let density : ℝ := H.card / (q : ℝ) ^ 3
      let triforce := (∑ e : Fin q × Fin q × Fin q,
        deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q : ℝ) ^ 6
      b * density ^ c ≤ triforce)
    {W : Type*} [Fintype W] [Nonempty W]
    (f : W → W → W → ℝ)
    (hf0 : ∀ x y z, 0 ≤ f x y z) (hf1 : ∀ x y z, f x y z ≤ 1) :
    let w : ℝ := Fintype.card W
    let μ : ℝ := (∑ x : W, ∑ y : W, ∑ z : W, f x y z) / w ^ 3
    let T : ℝ := (∑ x : W, ∑ y : W, ∑ z : W,
      (∑ z' : W, f x y z') * (∑ y' : W, f x y' z) * (∑ x' : W, f x' y z)) / w ^ 6
    b * μ ^ c ≤ T := by
  intro w μ T
  have hw_nat : 0 < Fintype.card W := Fintype.card_pos
  have hw : (0 : ℝ) < w := Nat.cast_pos.mpr hw_nat
  have hμ_nonneg : 0 ≤ μ := by
    dsimp only [μ]
    exact div_nonneg (sum_nonneg fun x _ => sum_nonneg fun y _ => sum_nonneg fun z _ => hf0 x y z)
      (pow_nonneg hw.le 3)
  have hT_nonneg : 0 ≤ T := by
    dsimp only [T]
    refine div_nonneg (sum_nonneg fun x _ => sum_nonneg fun y _ => sum_nonneg fun z _ => ?_)
      (pow_nonneg hw.le 6)
    exact mul_nonneg (mul_nonneg (sum_nonneg fun z' _ => hf0 x y z')
      (sum_nonneg fun y' _ => hf0 x y' z)) (sum_nonneg fun x' _ => hf0 x' y z)
  by_cases hμ0 : μ = 0
  · rw [hμ0, Real.zero_rpow (by linarith : c ≠ 0), mul_zero]
    exact hT_nonneg
  have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ0)
  -- For every R ≥ 1 with 1 / R ≤ μ, build the R-blowup hypergraph H on Fin (|W| * R).
  have hstep : ∀ R : ℕ, 0 < R → (1 : ℝ) / R ≤ μ → b * (μ - 1 / (R : ℝ)) ^ c ≤ T := by
    intro R hR hRμ
    have : NeZero R := ⟨Nat.pos_iff_ne_zero.mp hR⟩
    have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr hR
    set q : ℕ := Fintype.card W * R with hq_def
    have hq_pos_nat : 0 < q := Nat.mul_pos hw_nat hR
    have hq_cast : (q : ℝ) = w * (R : ℝ) := by simp [hq_def, w]
    let e : W × Fin R ≃ Fin q :=
      ((Fintype.equivFin W).prodCongr (Equiv.refl (Fin R))).trans finProdFinEquiv
    let t : W → W → W → ℕ := fun x y z => ⌊(R : ℝ) * f x y z⌋₊
    have ht_le_R : ∀ x y z, t x y z ≤ R := fun x y z => by
      dsimp only [t]
      have hle : (R : ℝ) * f x y z ≤ (R : ℝ) := by nlinarith [hf1 x y z]
      exact Nat.floor_le_of_le (by exact_mod_cast hle)
    have ht_le : ∀ x y z, (t x y z : ℝ) ≤ (R : ℝ) * f x y z := fun x y z =>
      Nat.floor_le (mul_nonneg hR_pos.le (hf0 x y z))
    have ht_ge : ∀ x y z, (R : ℝ) * f x y z - 1 ≤ (t x y z : ℝ) := fun x y z => by
      have := Nat.lt_floor_add_one ((R : ℝ) * f x y z)
      linarith
    let H : Finset (Fin q × Fin q × Fin q) :=
      univ.filter (fun p =>
        let xa := e.symm p.1
        let yb := e.symm p.2.1
        let zc := e.symm p.2.2
        (xa.2 + yb.2 + zc.2).val < t xa.1 yb.1 zc.1)
    have hHspec := hH q hq_pos_nat H
    dsimp only at hHspec
    -- Compute the three projection degrees.
    have hdeg_xy : ∀ (x : W) (a : Fin R) (y : W) (b₀ : Fin R),
        ((H.filter (fun p => (p.1, p.2.1) = (e (x, a), e (y, b₀)))).card : ℝ) =
          ∑ z : W, (t x y z : ℝ) := by
      intro x a y b₀
      have hcard : (H.filter (fun p => (p.1, p.2.1) = (e (x, a), e (y, b₀)))).card =
          ∑ z : W, t x y z := by
        have h1 : (H.filter (fun p => (p.1, p.2.1) = (e (x, a), e (y, b₀)))).card =
            (univ.filter (fun zc : W × Fin R => (a + b₀ + zc.2).val < t x y zc.1)).card := by
          refine Finset.card_bij (fun p _ => e.symm p.2.2) ?_ ?_ ?_
          · intro p hp
            simp only [H, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hp ⊢
            rcases hp with ⟨hpH, hp1, hp2⟩
            rw [hp1, hp2, e.symm_apply_apply, e.symm_apply_apply] at hpH
            exact hpH
          · intro p₁ hp₁ p₂ hp₂ h
            simp only [mem_filter, Prod.mk.injEq] at hp₁ hp₂
            exact Prod.ext (hp₁.2.1.trans hp₂.2.1.symm)
              (Prod.ext (hp₁.2.2.trans hp₂.2.2.symm) (e.symm.injective h))
          · intro zc hzc
            refine ⟨(e (x, a), e (y, b₀), e zc), ?_, e.symm_apply_apply zc⟩
            simp only [H, mem_filter, mem_univ, true_and, e.symm_apply_apply] at hzc ⊢
            exact ⟨hzc, trivial⟩
        rw [h1]
        have h2 : (univ.filter (fun zc : W × Fin R => (a + b₀ + zc.2).val < t x y zc.1)).card =
            ∑ z : W, (univ.filter (fun c₀ : Fin R => (a + b₀ + c₀).val < t x y z)).card := by
          rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun z _ => (Finset.card_filter _ _).symm
        rw [h2]
        refine Finset.sum_congr rfl fun z _ => card_fin_shift_lt R (a + b₀) (t x y z) (ht_le_R x y z)
      exact_mod_cast hcard
    have hdeg_xz : ∀ (x : W) (a : Fin R) (z : W) (c₀ : Fin R),
        ((H.filter (fun p => (p.1, p.2.2) = (e (x, a), e (z, c₀)))).card : ℝ) =
          ∑ y : W, (t x y z : ℝ) := by
      intro x a z c₀
      have hcard : (H.filter (fun p => (p.1, p.2.2) = (e (x, a), e (z, c₀)))).card =
          ∑ y : W, t x y z := by
        have h1 : (H.filter (fun p => (p.1, p.2.2) = (e (x, a), e (z, c₀)))).card =
            (univ.filter (fun yb : W × Fin R => (a + c₀ + yb.2).val < t x yb.1 z)).card := by
          refine Finset.card_bij (fun p _ => e.symm p.2.1) ?_ ?_ ?_
          · intro p hp
            simp only [H, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hp ⊢
            rcases hp with ⟨hpH, hp1, hp2⟩
            rw [hp1, hp2, e.symm_apply_apply, e.symm_apply_apply] at hpH
            convert hpH using 2
            abel
          · intro p₁ hp₁ p₂ hp₂ h
            simp only [mem_filter, Prod.mk.injEq] at hp₁ hp₂
            exact Prod.ext (hp₁.2.1.trans hp₂.2.1.symm)
              (Prod.ext (e.symm.injective h) (hp₁.2.2.trans hp₂.2.2.symm))
          · intro yb hyb
            refine ⟨(e (x, a), e yb, e (z, c₀)), ?_, e.symm_apply_apply yb⟩
            simp only [H, mem_filter, mem_univ, true_and, e.symm_apply_apply] at hyb ⊢
            refine ⟨?_, trivial⟩
            convert hyb using 2
            abel
        rw [h1]
        have h2 : (univ.filter (fun yb : W × Fin R => (a + c₀ + yb.2).val < t x yb.1 z)).card =
            ∑ y : W, (univ.filter (fun b₀ : Fin R => (a + c₀ + b₀).val < t x y z)).card := by
          rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun y _ => (Finset.card_filter _ _).symm
        rw [h2]
        refine Finset.sum_congr rfl fun y _ => card_fin_shift_lt R (a + c₀) (t x y z) (ht_le_R x y z)
      exact_mod_cast hcard
    have hdeg_yz : ∀ (y : W) (b₀ : Fin R) (z : W) (c₀ : Fin R),
        ((H.filter (fun p => (p.2.1, p.2.2) = (e (y, b₀), e (z, c₀)))).card : ℝ) =
          ∑ x : W, (t x y z : ℝ) := by
      intro y b₀ z c₀
      have hcard : (H.filter (fun p => (p.2.1, p.2.2) = (e (y, b₀), e (z, c₀)))).card =
          ∑ x : W, t x y z := by
        have h1 : (H.filter (fun p => (p.2.1, p.2.2) = (e (y, b₀), e (z, c₀)))).card =
            (univ.filter (fun xa : W × Fin R => (b₀ + c₀ + xa.2).val < t xa.1 y z)).card := by
          refine Finset.card_bij (fun p _ => e.symm p.1) ?_ ?_ ?_
          · intro p hp
            simp only [H, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hp ⊢
            rcases hp with ⟨hpH, hp1, hp2⟩
            rw [hp1, hp2, e.symm_apply_apply, e.symm_apply_apply] at hpH
            convert hpH using 2
            abel
          · intro p₁ hp₁ p₂ hp₂ h
            simp only [mem_filter, Prod.mk.injEq] at hp₁ hp₂
            exact Prod.ext (e.symm.injective h)
              (Prod.ext (hp₁.2.1.trans hp₂.2.1.symm) (hp₁.2.2.trans hp₂.2.2.symm))
          · intro xa hxa
            refine ⟨(e xa, e (y, b₀), e (z, c₀)), ?_, e.symm_apply_apply xa⟩
            simp only [H, mem_filter, mem_univ, true_and, e.symm_apply_apply] at hxa ⊢
            refine ⟨?_, trivial⟩
            convert hxa using 2
            abel
        rw [h1]
        have h2 : (univ.filter (fun xa : W × Fin R => (b₀ + c₀ + xa.2).val < t xa.1 y z)).card =
            ∑ x : W, (univ.filter (fun a : Fin R => (b₀ + c₀ + a).val < t x y z)).card := by
          rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
        rw [h2]
        refine Finset.sum_congr rfl fun x _ => card_fin_shift_lt R (b₀ + c₀) (t x y z) (ht_le_R x y z)
      exact_mod_cast hcard
    -- Compute density lower bound: μ - 1/R ≤ H.card / q^3.
    have hHcard : (H.card : ℝ) = (R : ℝ) ^ 2 * ∑ x : W, ∑ y : W, ∑ z : W, (t x y z : ℝ) := by
      have hsum : (H.card : ℝ) = ∑ u : Fin q, ∑ v : Fin q,
          ((H.filter (fun p => (p.1, p.2.1) = (u, v))).card : ℝ) := by
        have hnat : H.card = ∑ u : Fin q, ∑ v : Fin q,
            (H.filter (fun p => (p.1, p.2.1) = (u, v))).card := by
          simp_rw [Finset.card_filter]
          calc H.card = ∑ _p ∈ H, (1 : ℕ) := by simp
            _ = ∑ p ∈ H, ∑ u : Fin q, ∑ v : Fin q, if (p.1, p.2.1) = (u, v) then 1 else 0 := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_eq_single p.1]
              · rw [Finset.sum_eq_single p.2.1]
                · simp
                · intro v _ hv; simp [hv.symm]
                · intro h; exact absurd (mem_univ _) h
              · intro u _ hu
                refine Finset.sum_eq_zero fun v _ => ?_
                simp [hu.symm]
              · intro h; exact absurd (mem_univ _) h
            _ = ∑ u : Fin q, ∑ p ∈ H, ∑ v : Fin q, if (p.1, p.2.1) = (u, v) then 1 else 0 := by
              rw [Finset.sum_comm]
            _ = ∑ u : Fin q, ∑ v : Fin q, ∑ p ∈ H, if (p.1, p.2.1) = (u, v) then 1 else 0 := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
        exact_mod_cast hnat
      rw [hsum]
      rw [← Equiv.sum_comp e]
      simp_rw [← Equiv.sum_comp e, Fintype.sum_prod_type, hdeg_xy]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring
    have hdens : μ - 1 / (R : ℝ) ≤ (H.card : ℝ) / (q : ℝ) ^ 3 := by
      rw [hHcard, hq_cast]
      have hsum_ge : ∑ x : W, ∑ y : W, ∑ z : W, ((R : ℝ) * f x y z - 1) ≤
          ∑ x : W, ∑ y : W, ∑ z : W, (t x y z : ℝ) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => sum_le_sum fun z _ => ht_ge x y z
      have hsimp : ∑ x : W, ∑ y : W, ∑ z : W, ((R : ℝ) * f x y z - 1) =
          (R : ℝ) * (∑ x : W, ∑ y : W, ∑ z : W, f x y z) - w ^ 3 := by
        simp [Finset.sum_sub_distrib, ← Finset.mul_sum, w]
        ring
      rw [hsimp] at hsum_ge
      dsimp only [μ]
      have hdiv : (R : ℝ) ^ 2 * ((R : ℝ) * (∑ x : W, ∑ y : W, ∑ z : W, f x y z) - w ^ 3) /
          (w * (R : ℝ)) ^ 3 ≤
          (R : ℝ) ^ 2 * (∑ x : W, ∑ y : W, ∑ z : W, (t x y z : ℝ)) / (w * (R : ℝ)) ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_ge (sq_nonneg _))
          (pow_nonneg (mul_pos hw hR_pos).le 3)
      have heq : (R : ℝ) ^ 2 * ((R : ℝ) * (∑ x : W, ∑ y : W, ∑ z : W, f x y z) - w ^ 3) /
          (w * (R : ℝ)) ^ 3 =
          (∑ x : W, ∑ y : W, ∑ z : W, f x y z) / w ^ 3 - 1 / (R : ℝ) := by
        field_simp [hw.ne', hR_pos.ne']
      linarith
    -- Compute triforce upper bound: triforce(H) ≤ T.
    have htrif : (∑ p : Fin q × Fin q × Fin q,
        ((H.filter (fun p' => (p'.1, p'.2.1) = (p.1, p.2.1))).card : ℝ) *
        ((H.filter (fun p' => (p'.1, p'.2.2) = (p.1, p.2.2))).card : ℝ) *
        ((H.filter (fun p' => (p'.2.1, p'.2.2) = (p.2.1, p.2.2))).card : ℝ)) / (q : ℝ) ^ 6 ≤ T := by
      have hrew : (∑ p : Fin q × Fin q × Fin q,
          ((H.filter (fun p' => (p'.1, p'.2.1) = (p.1, p.2.1))).card : ℝ) *
          ((H.filter (fun p' => (p'.1, p'.2.2) = (p.1, p.2.2))).card : ℝ) *
          ((H.filter (fun p' => (p'.2.1, p'.2.2) = (p.2.1, p.2.2))).card : ℝ)) =
          (R : ℝ) ^ 3 * ∑ x : W, ∑ y : W, ∑ z : W,
            (∑ z' : W, (t x y z' : ℝ)) * (∑ y' : W, (t x y' z : ℝ)) * (∑ x' : W, (t x' y z : ℝ)) := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        rw [← Equiv.sum_comp e]
        simp_rw [← Equiv.sum_comp e, Fintype.sum_prod_type, hdeg_xy, hdeg_xz, hdeg_yz]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
      rw [hrew, hq_cast]
      have hle_sum : ∑ x : W, ∑ y : W, ∑ z : W,
          (∑ z' : W, (t x y z' : ℝ)) * (∑ y' : W, (t x y' z : ℝ)) * (∑ x' : W, (t x' y z : ℝ)) ≤
          (R : ℝ) ^ 3 * ∑ x : W, ∑ y : W, ∑ z : W,
            (∑ z' : W, f x y z') * (∑ y' : W, f x y' z) * (∑ x' : W, f x' y z) := by
        rw [Finset.mul_sum]
        refine sum_le_sum fun x _ => ?_
        rw [Finset.mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [Finset.mul_sum]
        refine sum_le_sum fun z _ => ?_
        have h1 : ∑ z' : W, (t x y z' : ℝ) ≤ (R : ℝ) * ∑ z' : W, f x y z' := by
          rw [Finset.mul_sum]; exact sum_le_sum fun z' _ => ht_le x y z'
        have h2 : ∑ y' : W, (t x y' z : ℝ) ≤ (R : ℝ) * ∑ y' : W, f x y' z := by
          rw [Finset.mul_sum]; exact sum_le_sum fun y' _ => ht_le x y' z
        have h3 : ∑ x' : W, (t x' y z : ℝ) ≤ (R : ℝ) * ∑ x' : W, f x' y z := by
          rw [Finset.mul_sum]; exact sum_le_sum fun x' _ => ht_le x' y z
        have h10 : 0 ≤ ∑ z' : W, (t x y z' : ℝ) := sum_nonneg fun z' _ => Nat.cast_nonneg _
        have h20 : 0 ≤ ∑ y' : W, (t x y' z : ℝ) := sum_nonneg fun y' _ => Nat.cast_nonneg _
        have h30 : 0 ≤ ∑ x' : W, (t x' y z : ℝ) := sum_nonneg fun x' _ => Nat.cast_nonneg _
        have hmul := mul_le_mul (mul_le_mul h1 h2 h20 (h10.trans h1)) h3 h30
          (mul_nonneg (h10.trans h1) (h20.trans h2))
        linarith
      dsimp only [T]
      have hdiv : (R : ℝ) ^ 3 *
          (∑ x : W, ∑ y : W, ∑ z : W,
            (∑ z' : W, (t x y z' : ℝ)) * (∑ y' : W, (t x y' z : ℝ)) * (∑ x' : W, (t x' y z : ℝ))) /
          (w * (R : ℝ)) ^ 6 ≤
          (R : ℝ) ^ 3 * ((R : ℝ) ^ 3 * ∑ x : W, ∑ y : W, ∑ z : W,
            (∑ z' : W, f x y z') * (∑ y' : W, f x y' z) * (∑ x' : W, f x' y z)) /
          (w * (R : ℝ)) ^ 6 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle_sum (pow_nonneg hR_pos.le 3))
          (pow_nonneg (mul_pos hw hR_pos).le 6)
      have heq : (R : ℝ) ^ 3 * ((R : ℝ) ^ 3 * ∑ x : W, ∑ y : W, ∑ z : W,
          (∑ z' : W, f x y z') * (∑ y' : W, f x y' z) * (∑ x' : W, f x' y z)) /
          (w * (R : ℝ)) ^ 6 =
          (∑ x : W, ∑ y : W, ∑ z : W,
            (∑ z' : W, f x y z') * (∑ y' : W, f x y' z) * (∑ x' : W, f x' y z)) / w ^ 6 := by
        field_simp [hw.ne', hR_pos.ne']
      linarith
    have hpow : (μ - 1 / (R : ℝ)) ^ c ≤ ((H.card : ℝ) / (q : ℝ) ^ 3) ^ c :=
      Real.rpow_le_rpow (by linarith) hdens (by linarith)
    calc b * (μ - 1 / (R : ℝ)) ^ c
        ≤ b * ((H.card : ℝ) / (q : ℝ) ^ 3) ^ c := mul_le_mul_of_nonneg_left hpow hb.le
      _ ≤ (∑ p : Fin q × Fin q × Fin q,
            ((H.filter (fun p' => (p'.1, p'.2.1) = (p.1, p.2.1))).card : ℝ) *
            ((H.filter (fun p' => (p'.1, p'.2.2) = (p.1, p.2.2))).card : ℝ) *
            ((H.filter (fun p' => (p'.2.1, p'.2.2) = (p.2.1, p.2.2))).card : ℝ)) / (q : ℝ) ^ 6 :=
          hHspec
      _ ≤ T := htrif
  -- Take the limit as R → ∞.
  have htend_inv : Tendsto (fun R : ℕ => (1 : ℝ) / (R : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have htend_sub : Tendsto (fun R : ℕ => μ - 1 / (R : ℝ)) atTop (𝓝 μ) := by
    simpa using tendsto_const_nhds.sub htend_inv
  have htend : Tendsto (fun R : ℕ => b * (μ - 1 / (R : ℝ)) ^ c) atTop (𝓝 (b * μ ^ c)) :=
    tendsto_const_nhds.mul (htend_sub.rpow_const (Or.inl hμ_pos.ne'))
  have hev : ∀ᶠ R : ℕ in atTop, b * (μ - 1 / (R : ℝ)) ^ c ≤ T := by
    have h1 : ∀ᶠ R : ℕ in atTop, (1 : ℝ) / (R : ℝ) ≤ μ :=
      htend_inv.eventually (Iic_mem_nhds hμ_pos)
    filter_upwards [eventually_gt_atTop 0, h1] with R hR hRμ
    exact hstep R hR hRμ
  exact le_of_tendsto htend hev

end WeightedTriforce

/- ## Section 2: Variance / Energy Increment & Bipartite Triangle Counting -/

section Combinatorics

/-- Density of `M` inside `S` (0 if `S` is empty). -/
private noncomputable def setDens {α : Type*} [DecidableEq α] (S M : Finset α) : ℝ :=
  if S.card = 0 then 0 else ((M ∩ S).card : ℝ) / (S.card : ℝ)

private lemma setDens_nonneg {α : Type*} [DecidableEq α] (S M : Finset α) : 0 ≤ setDens S M := by
  unfold setDens
  split_ifs
  · exact le_rfl
  · positivity

private lemma setDens_le_one {α : Type*} [DecidableEq α] (S M : Finset α) : setDens S M ≤ 1 := by
  unfold setDens
  split_ifs with h
  · norm_num
  · rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right

private lemma card_mul_setDens {α : Type*} [DecidableEq α] (S M : Finset α) :
    (S.card : ℝ) * setDens S M = ((M ∩ S).card : ℝ) := by
  unfold setDens
  split_ifs with h
  · have hS : S = ∅ := Finset.card_eq_zero.mp h
    simp [hS]
  · field_simp [Nat.cast_ne_zero.mpr h]

/-- Exact variance identity for partitioning `S` by a label map `φ : α → ι`. -/
private lemma partition_variance_eq {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S M : Finset α) (φ : α → ι) :
    ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M) ^ 2 =
    (S.card : ℝ) * (setDens S M) ^ 2 +
    ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M - setDens S M) ^ 2 := by
  set μ := setDens S M
  have hcard_sum : ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) = (S.card : ℝ) := by
    have hnat : ∑ i : ι, (S.filter (fun x => φ x = i)).card = S.card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      simp
    exact_mod_cast hnat
  have hM_sum : ∑ i : ι, ((M ∩ S.filter (fun x => φ x = i)).card : ℝ) = ((M ∩ S).card : ℝ) := by
    have hnat : ∑ i : ι, (M ∩ S.filter (fun x => φ x = i)).card = (M ∩ S).card := by
      have heq : ∀ i : ι, M ∩ S.filter (fun x => φ x = i) = (M ∩ S).filter (fun x => φ x = i) := by
        intro i; ext x; simp [and_assoc]
      simp_rw [heq, Finset.card_filter]
      rw [Finset.sum_comm]
      simp
    exact_mod_cast hnat
  have hexp : ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M - μ) ^ 2 =
      (∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
        (setDens (S.filter (fun x => φ x = i)) M) ^ 2) -
      2 * μ * (∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
        setDens (S.filter (fun x => φ x = i)) M) +
      μ ^ 2 * (∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ)) := by
    calc ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
          (setDens (S.filter (fun x => φ x = i)) M - μ) ^ 2
        = ∑ i : ι, (((S.filter (fun x => φ x = i)).card : ℝ) *
            (setDens (S.filter (fun x => φ x = i)) M) ^ 2 -
            2 * μ * (((S.filter (fun x => φ x = i)).card : ℝ) *
              setDens (S.filter (fun x => φ x = i)) M) +
            μ ^ 2 * ((S.filter (fun x => φ x = i)).card : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp_rw [card_mul_setDens] at hexp
  rw [hM_sum, hcard_sum, ← card_mul_setDens S M] at hexp
  linarith

/-- Partitioning never decreases weighted squared density. -/
private lemma partition_energy_mono {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S M : Finset α) (φ : α → ι) :
    (S.card : ℝ) * (setDens S M) ^ 2 ≤
    ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M) ^ 2 := by
  rw [partition_variance_eq S M φ]
  have hnonneg : 0 ≤ ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M - setDens S M) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

/-- Single-piece energy increment bound. -/
private lemma partition_energy_increment {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S M : Finset α) (φ : α → ι) (i₀ : ι) :
    (S.card : ℝ) * (setDens S M) ^ 2 +
    ((S.filter (fun x => φ x = i₀)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i₀)) M - setDens S M) ^ 2 ≤
    ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M) ^ 2 := by
  rw [partition_variance_eq S M φ]
  have hle : ((S.filter (fun x => φ x = i₀)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i₀)) M - setDens S M) ^ 2 ≤
      ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
        (setDens (S.filter (fun x => φ x = i)) M - setDens S M) ^ 2 :=
    Finset.single_le_sum
      (f := fun i => ((S.filter (fun x => φ x = i)).card : ℝ) *
        (setDens (S.filter (fun x => φ x = i)) M - setDens S M) ^ 2)
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (mem_univ i₀)
  linarith

/-- Refining a label map `φ` by `ψ` never decreases weighted squared density. -/
private lemma refinement_energy_mono {α ι κ : Type*} [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S M : Finset α) (φ : α → ι) (ψ : α → κ) (proj : κ → ι)
    (hproj : ∀ x ∈ S, proj (ψ x) = φ x) :
    ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
      (setDens (S.filter (fun x => φ x = i)) M) ^ 2 ≤
    ∑ k : κ, ((S.filter (fun x => ψ x = k)).card : ℝ) *
      (setDens (S.filter (fun x => ψ x = k)) M) ^ 2 := by
  have h1 : ∀ i : ι,
      ((S.filter (fun x => φ x = i)).card : ℝ) * (setDens (S.filter (fun x => φ x = i)) M) ^ 2 ≤
      ∑ k ∈ univ.filter (fun k : κ => proj k = i),
        ((S.filter (fun x => ψ x = k)).card : ℝ) * (setDens (S.filter (fun x => ψ x = k)) M) ^ 2 := by
    intro i
    calc ((S.filter (fun x => φ x = i)).card : ℝ) * (setDens (S.filter (fun x => φ x = i)) M) ^ 2
        ≤ ∑ k : κ, (((S.filter (fun x => φ x = i)).filter (fun x => ψ x = k)).card : ℝ) *
            (setDens ((S.filter (fun x => φ x = i)).filter (fun x => ψ x = k)) M) ^ 2 :=
          partition_energy_mono (S.filter (fun x => φ x = i)) M ψ
      _ = ∑ k ∈ univ.filter (fun k : κ => proj k = i),
            ((S.filter (fun x => ψ x = k)).card : ℝ) *
              (setDens (S.filter (fun x => ψ x = k)) M) ^ 2 := by
          rw [← Finset.sum_subset (Finset.filter_subset (fun k : κ => proj k = i) univ)]
          · refine Finset.sum_congr rfl fun k hk => ?_
            simp only [mem_filter, mem_univ, true_and] at hk
            have heq : (S.filter (fun x => φ x = i)).filter (fun x => ψ x = k) =
                S.filter (fun x => ψ x = k) := by
              ext x
              simp only [mem_filter]
              constructor
              · rintro ⟨⟨hx, _⟩, hψ⟩; exact ⟨hx, hψ⟩
              · rintro ⟨hx, hψ⟩; exact ⟨⟨hx, by rw [← hproj x hx, hψ, hk]⟩, hψ⟩
            rw [heq]
          · intro k _ hk
            simp only [mem_filter, mem_univ, true_and] at hk
            have hemp : (S.filter (fun x => φ x = i)).filter (fun x => ψ x = k) = ∅ := by
              ext x
              simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
              rintro ⟨hx, hφ⟩ hψ
              exact hk (by rw [← hψ, hproj x hx, hφ])
            simp [hemp]
  calc ∑ i : ι, ((S.filter (fun x => φ x = i)).card : ℝ) *
        (setDens (S.filter (fun x => φ x = i)) M) ^ 2
      ≤ ∑ i : ι, ∑ k ∈ univ.filter (fun k : κ => proj k = i),
          ((S.filter (fun x => ψ x = k)).card : ℝ) * (setDens (S.filter (fun x => ψ x = k)) M) ^ 2 :=
        sum_le_sum fun i _ => h1 i
    _ = ∑ k : κ, ((S.filter (fun x => ψ x = k)).card : ℝ) *
          (setDens (S.filter (fun x => ψ x = k)) M) ^ 2 := by
        exact Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := proj)
          (f := fun k => ((S.filter (fun x => ψ x = k)).card : ℝ) *
            (setDens (S.filter (fun x => ψ x = k)) M) ^ 2)
          (fun _ _ => mem_univ _)

/-- Bipartite edge density between `X` and `Y`. -/
private noncomputable def edgeDens {α β : Type*}
    (X : Finset α) (Y : Finset β) (e : α → β → Prop) : ℝ :=
  if X.card = 0 ∨ Y.card = 0 then 0
  else (((X ×ˢ Y).filter (fun p => e p.1 p.2)).card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

private lemma edgeDens_eq_setDens {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (e : α → β → Prop) :
    edgeDens X Y e = setDens (X ×ˢ Y) ((X ×ˢ Y).filter (fun p => e p.1 p.2)) := by
  unfold edgeDens setDens
  have hcard : (X ×ˢ Y).card = X.card * Y.card := Finset.card_product X Y
  have hzero : (X.card = 0 ∨ Y.card = 0) ↔ (X ×ˢ Y).card = 0 := by
    rw [hcard, mul_eq_zero]
  have hinter : ((X ×ˢ Y).filter (fun p => e p.1 p.2) ∩ (X ×ˢ Y)).card =
      ((X ×ˢ Y).filter (fun p => e p.1 p.2)).card := by
    congr 1
    exact Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hzero.mp h1) h2
  · exact absurd (hzero.mpr h2) h1
  · rw [hinter, hcard, Nat.cast_mul]

private lemma edgeDens_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (e : α → β → Prop) : 0 ≤ edgeDens X Y e := by
  rw [edgeDens_eq_setDens]; exact setDens_nonneg _ _

private lemma edgeDens_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (e : α → β → Prop) : edgeDens X Y e ≤ 1 := by
  rw [edgeDens_eq_setDens]; exact setDens_le_one _ _

/-- `ε`-quasirandomness of a bipartite graph on `X × Y`. -/
private def IsQuasirandom {α β : Type*} (ε : ℝ)
    (X : Finset α) (Y : Finset β) (e : α → β → Prop) : Prop :=
  ∀ X' ⊆ X, ∀ Y' ⊆ Y,
    ε * (X.card : ℝ) ≤ (X'.card : ℝ) →
    ε * (Y.card : ℝ) ≤ (Y'.card : ℝ) →
    |edgeDens X' Y' e - edgeDens X Y e| ≤ ε

private lemma poly_tri_bound {ε a b c : ℝ} (hε : 0 < ε)
    (ha0 : 2 * ε ≤ a) (ha1 : a ≤ 1)
    (hb0 : 2 * ε ≤ b) (hb1 : b ≤ 1)
    (hc0 : 2 * ε ≤ c) (hc1 : c ≤ 1) :
    a * b * c - 5 * ε ≤ (1 - 2 * ε) * (a - ε) * (b - ε) * (c - ε) := by
  have h1 : 0 ≤ 1 - 2 * ε := by linarith
  have hdiff : a * b * c - (1 - 2 * ε) * (a - ε) * (b - ε) * (c - ε) =
      2 * ε * (a * b * c) +
      (1 - 2 * ε) * ε * (b * c) +
      (1 - 2 * ε) * (a - ε) * ε * c +
      (1 - 2 * ε) * (a - ε) * (b - ε) * ε := by ring
  have t1 : a * b * c ≤ 1 := by
    have : a * b ≤ 1 := by nlinarith
    nlinarith
  have t2 : (1 - 2 * ε) * (b * c) ≤ 1 := by
    have : b * c ≤ 1 := by nlinarith
    nlinarith
  have t3 : (1 - 2 * ε) * (a - ε) * c ≤ 1 := by
    have : (1 - 2 * ε) * (a - ε) ≤ 1 := by nlinarith
    nlinarith
  have t4 : (1 - 2 * ε) * (a - ε) * (b - ε) ≤ 1 := by
    have : (1 - 2 * ε) * (a - ε) ≤ 1 := by nlinarith
    nlinarith
  nlinarith

/-- Bipartite triangle counting lemma. -/
private lemma triangle_counting_lemma {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {ε : ℝ} (hε : 0 < ε)
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (eXY : α → β → Prop) (eXZ : α → γ → Prop) (eYZ : β → γ → Prop)
    (hXY : IsQuasirandom ε X Y eXY)
    (hXZ : IsQuasirandom ε X Z eXZ)
    (hYZ : IsQuasirandom ε Y Z eYZ) :
    (edgeDens X Y eXY * edgeDens X Z eXZ * edgeDens Y Z eYZ - 5 * ε) *
      (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤
    (((X ×ˢ Y ×ˢ Z).filter (fun t => eXY t.1 t.2.1 ∧ eXZ t.1 t.2.2 ∧ eYZ t.2.1 t.2.2)).card : ℝ) := by
  set dXY := edgeDens X Y eXY
  set dXZ := edgeDens X Z eXZ
  set dYZ := edgeDens Y Z eYZ
  have hdXY0 : 0 ≤ dXY := edgeDens_nonneg X Y eXY
  have hdXZ0 : 0 ≤ dXZ := edgeDens_nonneg X Z eXZ
  have hdYZ0 : 0 ≤ dYZ := edgeDens_nonneg Y Z eYZ
  have hdXY1 : dXY ≤ 1 := edgeDens_le_one X Y eXY
  have hdXZ1 : dXZ ≤ 1 := edgeDens_le_one X Z eXZ
  have hdYZ1 : dYZ ≤ 1 := edgeDens_le_one Y Z eYZ
  by_cases hcard0 : X.card = 0 ∨ Y.card = 0 ∨ Z.card = 0
  · rcases hcard0 with h | h | h <;> simp [h]
  push Not at hcard0
  rcases hcard0 with ⟨hX0, hY0, hZ0⟩
  have hXpos : (0 : ℝ) < X.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hX0)
  have hYpos : (0 : ℝ) < Y.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hY0)
  have hZpos : (0 : ℝ) < Z.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hZ0)
  by_cases hsmall : dXY < 2 * ε ∨ dXZ < 2 * ε ∨ dYZ < 2 * ε
  · have hprod_le : dXY * dXZ * dYZ ≤ 5 * ε := by
      rcases hsmall with h | h | h
      · have h1 : dXY * dXZ ≤ dXY * 1 := mul_le_mul_of_nonneg_left hdXZ1 hdXY0
        have h2 : dXY * dXZ * dYZ ≤ (dXY * dXZ) * 1 :=
          mul_le_mul_of_nonneg_left hdYZ1 (mul_nonneg hdXY0 hdXZ0)
        linarith
      · have h1 : dXY * dXZ ≤ 1 * dXZ := mul_le_mul_of_nonneg_right hdXY1 hdXZ0
        have h2 : dXY * dXZ * dYZ ≤ (dXY * dXZ) * 1 :=
          mul_le_mul_of_nonneg_left hdYZ1 (mul_nonneg hdXY0 hdXZ0)
        linarith
      · have h1 : dXY * dXZ ≤ 1 * 1 := mul_le_mul hdXY1 hdXZ1 hdXZ0 zero_le_one
        have h2 : dXY * dXZ * dYZ ≤ 1 * dYZ := mul_le_mul_of_nonneg_right (by linarith) hdYZ0
        linarith
    have hneg : (dXY * dXZ * dYZ - 5 * ε) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤ 0 := by
      have : dXY * dXZ * dYZ - 5 * ε ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg this hXpos.le) hYpos.le)
        hZpos.le
    exact hneg.trans (Nat.cast_nonneg _)
  push Not at hsmall
  rcases hsmall with ⟨h2XY, h2XZ, h2YZ⟩
  have hε_le_half : ε ≤ 1 / 2 := by linarith
  have hε_le_one : ε ≤ 1 := by linarith
  -- Define neighborhoods and low-degree bad vertices.
  let NY : α → Finset β := fun x => Y.filter (fun y => eXY x y)
  let NZ : α → Finset γ := fun x => Z.filter (fun z => eXZ x z)
  let BY : Finset α := X.filter (fun x => ((NY x).card : ℝ) < (dXY - ε) * (Y.card : ℝ))
  let BZ : Finset α := X.filter (fun x => ((NZ x).card : ℝ) < (dXZ - ε) * (Z.card : ℝ))
  have hBY_lt : (BY.card : ℝ) < ε * (X.card : ℝ) := by
    by_contra hge
    push Not at hge
    have hBY_pos : (0 : ℝ) < BY.card := lt_of_lt_of_le (mul_pos hε hXpos) hge
    have hBY_ne : BY.card ≠ 0 := by exact_mod_cast hBY_pos.ne'
    have hqr := hXY BY (Finset.filter_subset _ _) Y Subset.rfl hge (by nlinarith)
    have hge_dens : dXY - ε ≤ edgeDens BY Y eXY := by
      have := (abs_le.mp hqr).1; linarith
    have hedge_sum : (((BY ×ˢ Y).filter (fun p => eXY p.1 p.2)).card : ℝ) =
        ∑ x ∈ BY, ((NY x).card : ℝ) := by
      have hnat : ((BY ×ˢ Y).filter (fun p => eXY p.1 p.2)).card = ∑ x ∈ BY, (NY x).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
      exact_mod_cast hnat
    have hlt_sum : ∑ x ∈ BY, ((NY x).card : ℝ) < (dXY - ε) * (BY.card : ℝ) * (Y.card : ℝ) := by
      have hne : BY.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hBY_ne)
      calc ∑ x ∈ BY, ((NY x).card : ℝ)
          < ∑ _x ∈ BY, ((dXY - ε) * (Y.card : ℝ)) :=
            Finset.sum_lt_sum_of_nonempty hne fun x hx => (Finset.mem_filter.mp hx).2
        _ = (dXY - ε) * (BY.card : ℝ) * (Y.card : ℝ) := by
            simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have hed : edgeDens BY Y eXY =
        (((BY ×ˢ Y).filter (fun p => eXY p.1 p.2)).card : ℝ) / ((BY.card : ℝ) * (Y.card : ℝ)) := by
      unfold edgeDens; simp [hBY_ne, hY0]
    rw [hed, hedge_sum, le_div_iff₀ (mul_pos hBY_pos hYpos)] at hge_dens
    linarith
  have hBZ_lt : (BZ.card : ℝ) < ε * (X.card : ℝ) := by
    by_contra hge
    push Not at hge
    have hBZ_pos : (0 : ℝ) < BZ.card := lt_of_lt_of_le (mul_pos hε hXpos) hge
    have hBZ_ne : BZ.card ≠ 0 := by exact_mod_cast hBZ_pos.ne'
    have hqr := hXZ BZ (Finset.filter_subset _ _) Z Subset.rfl hge (by nlinarith)
    have hge_dens : dXZ - ε ≤ edgeDens BZ Z eXZ := by
      have := (abs_le.mp hqr).1; linarith
    have hedge_sum : (((BZ ×ˢ Z).filter (fun p => eXZ p.1 p.2)).card : ℝ) =
        ∑ x ∈ BZ, ((NZ x).card : ℝ) := by
      have hnat : ((BZ ×ˢ Z).filter (fun p => eXZ p.1 p.2)).card = ∑ x ∈ BZ, (NZ x).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
      exact_mod_cast hnat
    have hlt_sum : ∑ x ∈ BZ, ((NZ x).card : ℝ) < (dXZ - ε) * (BZ.card : ℝ) * (Z.card : ℝ) := by
      have hne : BZ.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hBZ_ne)
      calc ∑ x ∈ BZ, ((NZ x).card : ℝ)
          < ∑ _x ∈ BZ, ((dXZ - ε) * (Z.card : ℝ)) :=
            Finset.sum_lt_sum_of_nonempty hne fun x hx => (Finset.mem_filter.mp hx).2
        _ = (dXZ - ε) * (BZ.card : ℝ) * (Z.card : ℝ) := by
            simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have hed : edgeDens BZ Z eXZ =
        (((BZ ×ˢ Z).filter (fun p => eXZ p.1 p.2)).card : ℝ) / ((BZ.card : ℝ) * (Z.card : ℝ)) := by
      unfold edgeDens; simp [hBZ_ne, hZ0]
    rw [hed, hedge_sum, le_div_iff₀ (mul_pos hBZ_pos hZpos)] at hge_dens
    linarith
  let Good : Finset α := X \ (BY ∪ BZ)
  have hGood_card : (1 - 2 * ε) * (X.card : ℝ) ≤ (Good.card : ℝ) := by
    have hsub : BY ∪ BZ ⊆ X := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcard : Good.card + (BY ∪ BZ).card = X.card := Finset.card_sdiff_add_card_eq_card hsub
    have hu : ((BY ∪ BZ).card : ℝ) ≤ (BY.card : ℝ) + (BZ.card : ℝ) := by
      exact_mod_cast Finset.card_union_le BY BZ
    have hcast : (Good.card : ℝ) + ((BY ∪ BZ).card : ℝ) = (X.card : ℝ) := by exact_mod_cast hcard
    linarith
  -- Count triangles for each good x ∈ Good.
  have hgood_tri : ∀ x ∈ Good,
      (dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ) ≤
      (((NY x ×ˢ NZ x).filter (fun p => eYZ p.1 p.2)).card : ℝ) := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxBY : x ∉ BY := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)
    have hxBZ : x ∉ BZ := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ h)
    have hNY_ge : (dXY - ε) * (Y.card : ℝ) ≤ ((NY x).card : ℝ) := by
      by_contra hlt; push Not at hlt
      exact hxBY (Finset.mem_filter.mpr ⟨hxX, hlt⟩)
    have hNZ_ge : (dXZ - ε) * (Z.card : ℝ) ≤ ((NZ x).card : ℝ) := by
      by_contra hlt; push Not at hlt
      exact hxBZ (Finset.mem_filter.mpr ⟨hxX, hlt⟩)
    have hNY_eps : ε * (Y.card : ℝ) ≤ ((NY x).card : ℝ) := by nlinarith
    have hNZ_eps : ε * (Z.card : ℝ) ≤ ((NZ x).card : ℝ) := by nlinarith
    have hNY_pos : (0 : ℝ) < (NY x).card := lt_of_lt_of_le (mul_pos hε hYpos) hNY_eps
    have hNZ_pos : (0 : ℝ) < (NZ x).card := lt_of_lt_of_le (mul_pos hε hZpos) hNZ_eps
    have hNY_ne : (NY x).card ≠ 0 := by exact_mod_cast hNY_pos.ne'
    have hNZ_ne : (NZ x).card ≠ 0 := by exact_mod_cast hNZ_pos.ne'
    have hqr := hYZ (NY x) (Finset.filter_subset _ _) (NZ x) (Finset.filter_subset _ _) hNY_eps hNZ_eps
    have hge_dens : dYZ - ε ≤ edgeDens (NY x) (NZ x) eYZ := by
      have := (abs_le.mp hqr).1; linarith
    have hed : edgeDens (NY x) (NZ x) eYZ =
        (((NY x ×ˢ NZ x).filter (fun p => eYZ p.1 p.2)).card : ℝ) /
        (((NY x).card : ℝ) * ((NZ x).card : ℝ)) := by
      unfold edgeDens; simp [hNY_ne, hNZ_ne]
    rw [hed, le_div_iff₀ (mul_pos hNY_pos hNZ_pos)] at hge_dens
    have hmul : (dXY - ε) * (Y.card : ℝ) * ((dXZ - ε) * (Z.card : ℝ)) ≤
        ((NY x).card : ℝ) * ((NZ x).card : ℝ) :=
      mul_le_mul hNY_ge hNZ_ge (mul_nonneg (by linarith) hZpos.le) hNY_pos.le
    have hmul2 : (dYZ - ε) * ((dXY - ε) * (Y.card : ℝ) * ((dXZ - ε) * (Z.card : ℝ))) ≤
        (dYZ - ε) * (((NY x).card : ℝ) * ((NZ x).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmul (by linarith)
    linarith
  -- Sum over x ∈ Good and compare with total triangles.
  have htri_sum : ∑ x ∈ Good, (((NY x ×ˢ NZ x).filter (fun p => eYZ p.1 p.2)).card : ℝ) ≤
      (((X ×ˢ Y ×ˢ Z).filter (fun t => eXY t.1 t.2.1 ∧ eXZ t.1 t.2.2 ∧ eYZ t.2.1 t.2.2)).card : ℝ) := by
    have hnat : ∑ x ∈ Good, ((NY x ×ˢ NZ x).filter (fun p => eYZ p.1 p.2)).card ≤
        ((X ×ˢ Y ×ˢ Z).filter (fun t => eXY t.1 t.2.1 ∧ eXZ t.1 t.2.2 ∧ eYZ t.2.1 t.2.2)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.sdiff_subset : Good ⊆ X))
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
      simp only [NY, NZ, Finset.sum_filter]
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases h1 : eXY x y
      · simp only [h1, if_true, true_and]
        refine Finset.sum_le_sum fun z _ => ?_
        by_cases h2 : eXZ x z <;> by_cases h3 : eYZ y z <;> simp [h2, h3]
      · simp only [h1, if_false, false_and, Finset.sum_const_zero, le_rfl]
    exact_mod_cast hnat
  -- Telescoping bound: dXY * dXZ * dYZ - 5 * ε ≤ (1 - 2 * ε) * (dXY - ε) * (dXZ - ε) * (dYZ - ε).
  have hpoly : dXY * dXZ * dYZ - 5 * ε ≤ (1 - 2 * ε) * (dXY - ε) * (dXZ - ε) * (dYZ - ε) :=
    poly_tri_bound hε h2XY hdXY1 h2XZ hdXZ1 h2YZ hdYZ1
  have hsum_ge : (1 - 2 * ε) * (dXY - ε) * (dXZ - ε) * (dYZ - ε) *
      (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤
      ∑ x ∈ Good, (((NY x ×ˢ NZ x).filter (fun p => eYZ p.1 p.2)).card : ℝ) := by
    calc (1 - 2 * ε) * (dXY - ε) * (dXZ - ε) * (dYZ - ε) *
          (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)
        = ((1 - 2 * ε) * (X.card : ℝ)) *
          ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) := by ring
      _ ≤ (Good.card : ℝ) *
          ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hGood_card
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
              hYpos.le) hZpos.le)
      _ = ∑ _x ∈ Good, ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Good, (((NY x ×ˢ NZ x).filter (fun p => eYZ p.1 p.2)).card : ℝ) :=
          sum_le_sum hgood_tri
  have hpoly_scaled : (dXY * dXZ * dYZ - 5 * ε) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤
      (1 - 2 * ε) * (dXY - ε) * (dXZ - ε) * (dYZ - ε) *
      (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly hXpos.le) hYpos.le) hZpos.le
  linarith

end Combinatorics

/- ## Section 3: Finite Fourier Analysis on Subspaces of `𝔽₂ n` -/

section Fourier

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma sum_zmod2 (f : ZMod 2 → ℝ) : ∑ b : ZMod 2, f b = f 0 + f 1 := by
  have huniv : (univ : Finset (ZMod 2)) = {0, 1} := by
    ext x; simp [zmod2_eq_zero_or_one x]
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]

/-- Standard dot product on `𝔽₂ n`. -/
private def dot {n : ℕ} (r x : 𝔽₂ n) : ZMod 2 :=
  ∑ i : Fin n, r i * x i

/-- Linear functional `x ↦ dot r x` on `𝔽₂ n`. -/
private def dotLM {n : ℕ} (r : 𝔽₂ n) : 𝔽₂ n →ₗ[ZMod 2] ZMod 2 where
  toFun := dot r
  map_add' x y := by
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

private lemma dot_add_left {n : ℕ} (r s x : 𝔽₂ n) : dot (r + s) x = dot r x + dot s x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {n : ℕ} (r x y : 𝔽₂ n) : dot r (x + y) = dot r x + dot r y :=
  (dotLM r).map_add x y

private lemma dot_zero_right {n : ℕ} (r : 𝔽₂ n) : dot r 0 = 0 :=
  (dotLM r).map_zero

private lemma f2_add_self {n : ℕ} (x : 𝔽₂ n) : x + x = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_eq_zero_or_one (x i) with h | h <;> rw [h] <;> decide

private lemma f2_neg_eq {n : ℕ} (x : 𝔽₂ n) : -x = x :=
  neg_eq_iff_add_eq_zero.mpr (f2_add_self x)

/-- Real-valued character `χ r x = (-1)^(dot r x)` on `𝔽₂ n`. -/
private def chi {n : ℕ} (r x : 𝔽₂ n) : ℝ :=
  if dot r x = 0 then 1 else -1

private lemma chi_add_right {n : ℕ} (r x y : 𝔽₂ n) :
    chi r (x + y) = chi r x * chi r y := by
  unfold chi
  rw [dot_add_right]
  rcases zmod2_eq_zero_or_one (dot r x) with hx | hx <;>
    rcases zmod2_eq_zero_or_one (dot r y) with hy | hy <;>
    rw [hx, hy] <;> norm_num
  decide

private lemma chi_add_left {n : ℕ} (r s x : 𝔽₂ n) :
    chi (r + s) x = chi r x * chi s x := by
  unfold chi
  rw [dot_add_left]
  rcases zmod2_eq_zero_or_one (dot r x) with hr | hr <;>
    rcases zmod2_eq_zero_or_one (dot s x) with hs | hs <;>
    rw [hr, hs] <;> norm_num
  decide

private lemma chi_zero_right {n : ℕ} (r : 𝔽₂ n) : chi r 0 = 1 := by
  simp [chi, dot_zero_right]

private lemma sum_chi_over_dual {n : ℕ} (x : 𝔽₂ n) :
    ∑ r : 𝔽₂ n, chi r x = if x = 0 then (Fintype.card (𝔽₂ n) : ℝ) else 0 := by
  split_ifs with hx
  · simp [hx, chi_zero_right]
  · have hex : ∃ i : Fin n, x i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (funext hall)
    rcases hex with ⟨i, hi⟩
    have hxi : x i = 1 := by
      rcases zmod2_eq_zero_or_one (x i) with h | h
      · exact absurd h hi
      · exact h
    let e : 𝔽₂ n := Pi.single i (1 : ZMod 2)
    have hdot_e : dot e x = 1 := by
      unfold dot
      rw [Finset.sum_eq_single i]
      · simp [e, hxi]
      · intro j _ hj
        simp [e, Pi.single_eq_of_ne hj]
      · intro hi'; exact absurd (mem_univ i) hi'
    have hchi_e : chi e x = -1 := by
      unfold chi; rw [hdot_e]; norm_num
    have hshift : ∑ r : 𝔽₂ n, chi r x = ∑ r : 𝔽₂ n, chi (e + r) x :=
      (Equiv.sum_comp (Equiv.addLeft e) (fun r => chi r x)).symm
    have hneg : ∑ r : 𝔽₂ n, chi (e + r) x = -(∑ r : 𝔽₂ n, chi r x) := by
      simp_rw [chi_add_left, hchi_e, neg_one_mul, Finset.sum_neg_distrib]
    linarith

/-- Annihilator of a subspace `W ≤ 𝔽₂ n` under `dot`. -/
private noncomputable def ann {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) : Finset (𝔽₂ n) :=
  univ.filter (fun r : 𝔽₂ n => ∀ w : W, dot r w.val = 0)

private lemma sum_chi_over_subspace {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) (r : 𝔽₂ n) :
    ∑ w : W, chi r w.val = if r ∈ ann W then (Fintype.card W : ℝ) else 0 := by
  split_ifs with hr
  · simp only [ann, mem_filter, mem_univ, true_and] at hr
    have : ∀ w : W, chi r w.val = 1 := fun w => by simp [chi, hr w]
    simp [this]
  · simp only [ann, mem_filter, mem_univ, true_and, not_forall] at hr
    rcases hr with ⟨w₀, hw₀⟩
    have hchi0 : chi r w₀.val = -1 := by simp [chi, hw₀]
    have hshift : ∑ w : W, chi r w.val = ∑ w : W, chi r (w₀ + w).val :=
      (Equiv.sum_comp (Equiv.addLeft w₀) (fun w : W => chi r w.val)).symm
    have hneg : ∑ w : W, chi r (w₀ + w).val = -(∑ w : W, chi r w.val) := by
      simp_rw [Submodule.coe_add, chi_add_right, hchi0, neg_one_mul, Finset.sum_neg_distrib]
    linarith

private lemma card_ann_mul_card_subspace {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    ((ann W).card : ℝ) * (Fintype.card W : ℝ) = (Fintype.card (𝔽₂ n) : ℝ) := by
  have h1 : ∑ w : W, ∑ r : 𝔽₂ n, chi r w.val = (Fintype.card (𝔽₂ n) : ℝ) := by
    simp_rw [sum_chi_over_dual]
    rw [Finset.sum_eq_single (0 : W)]
    · simp
    · intro w _ hw
      have hval : w.val ≠ 0 := fun h => hw (Subtype.ext h)
      simp [hval]
    · intro h; exact absurd (mem_univ (0 : W)) h
  have h2 : ∑ w : W, ∑ r : 𝔽₂ n, chi r w.val = ((ann W).card : ℝ) * (Fintype.card W : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [sum_chi_over_subspace]
    simp
  linarith

private lemma card_ann_pos {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    (0 : ℝ) < ((ann W).card : ℝ) := by
  have h := card_ann_mul_card_subspace W
  have hG : (0 : ℝ) < (Fintype.card (𝔽₂ n) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hW : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

/-- Normalized Fourier coefficient of `S : Finset W` at frequency `r : 𝔽₂ n`. -/
private noncomputable def fhat {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S : Finset W) (r : 𝔽₂ n) : ℝ :=
  (∑ w ∈ S, chi r w.val) / (Fintype.card W : ℝ)

private lemma fhat_of_mem_ann {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S : Finset W) {r : 𝔽₂ n} (hr : r ∈ ann W) :
    fhat W S r = (S.card : ℝ) / (Fintype.card W : ℝ) := by
  simp only [ann, mem_filter, mem_univ, true_and] at hr
  unfold fhat
  have : ∀ w ∈ S, chi r w.val = 1 := fun w _ => by simp [chi, hr w]
  rw [Finset.sum_congr rfl this]
  simp

/-- Parseval identity summed over all `r : 𝔽₂ n`. -/
private lemma parseval_subspace {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) (S : Finset W) :
    ∑ r : 𝔽₂ n, (fhat W S r) ^ 2 =
    ((ann W).card : ℝ) * ((S.card : ℝ) / (Fintype.card W : ℝ)) := by
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hexp : ∑ r : 𝔽₂ n, (fhat W S r) ^ 2 =
      (∑ w₁ ∈ S, ∑ w₂ ∈ S, ∑ r : 𝔽₂ n, chi r (w₁.val + w₂.val)) / (Fintype.card W : ℝ) ^ 2 := by
    unfold fhat
    simp_rw [div_pow, ← Finset.sum_div, sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun w₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w₂ _ => Finset.sum_congr rfl fun r _ => (chi_add_right r _ _).symm
  rw [hexp]
  have hinner : ∑ w₁ ∈ S, ∑ w₂ ∈ S, ∑ r : 𝔽₂ n, chi r (w₁.val + w₂.val) =
      (S.card : ℝ) * (Fintype.card (𝔽₂ n) : ℝ) := by
    simp_rw [sum_chi_over_dual]
    have h1 : ∀ w₁ ∈ S, ∑ w₂ ∈ S, (if w₁.val + w₂.val = 0 then (Fintype.card (𝔽₂ n) : ℝ) else 0) =
        (Fintype.card (𝔽₂ n) : ℝ) := by
      intro w₁ hw₁
      rw [Finset.sum_eq_single w₁]
      · simp [f2_add_self]
      · intro w₂ _ hne
        have hne0 : w₁.val + w₂.val ≠ 0 := by
          intro hsum
          have heq : w₂.val = w₁.val := by
            calc w₂.val = 0 + w₂.val := (zero_add _).symm
              _ = (w₁.val + w₁.val) + w₂.val := by rw [f2_add_self]
              _ = w₁.val + (w₁.val + w₂.val) := add_assoc _ _ _
              _ = w₁.val := by rw [hsum, add_zero]
          exact hne (Subtype.ext heq)
        simp [hne0]
      · intro h; exact absurd hw₁ h
    rw [Finset.sum_congr rfl h1]
    simp
  rw [hinner, ← card_ann_mul_card_subspace W]
  field_simp [hW_pos.ne']

/-- Fourier triple-convolution bound for uniform sets `B, C, D ⊆ W`. -/
private lemma triple_zero_sum_le {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (B C D : Finset W) {η : ℝ} (hη : 0 ≤ η)
    (hunif : ∀ r : 𝔽₂ n, r ∉ ann W → |fhat W B r| ≤ η) :
    (((B ×ˢ C ×ˢ D).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) /
      (Fintype.card W : ℝ) ^ 2 ≤
    ((B.card : ℝ) / (Fintype.card W : ℝ)) *
    ((C.card : ℝ) / (Fintype.card W : ℝ)) *
    ((D.card : ℝ) / (Fintype.card W : ℝ)) + η := by
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hann_pos : (0 : ℝ) < ((ann W).card : ℝ) := card_ann_pos W
  -- Triple sum identity.
  have htriple : ∑ r : 𝔽₂ n, fhat W B r * fhat W C r * fhat W D r =
      ((ann W).card : ℝ) *
      ((((B ×ˢ C ×ˢ D).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) /
        (Fintype.card W : ℝ) ^ 2) := by
    have hexp : ∑ r : 𝔽₂ n, fhat W B r * fhat W C r * fhat W D r =
        (∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, ∑ r : 𝔽₂ n, chi r (a.val + b.val + c.val)) /
        (Fintype.card W : ℝ) ^ 3 := by
      unfold fhat
      have hmul : ∀ r : 𝔽₂ n,
          ((∑ a ∈ B, chi r a.val) / (Fintype.card W : ℝ)) *
          ((∑ b ∈ C, chi r b.val) / (Fintype.card W : ℝ)) *
          ((∑ c ∈ D, chi r c.val) / (Fintype.card W : ℝ)) =
          (∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, chi r (a.val + b.val + c.val)) /
            (Fintype.card W : ℝ) ^ 3 := by
        intro r
        have hnum : (∑ a ∈ B, chi r a.val) * (∑ b ∈ C, chi r b.val) * (∑ c ∈ D, chi r c.val) =
            ∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, chi r (a.val + b.val + c.val) := by
          calc (∑ a ∈ B, chi r a.val) * (∑ b ∈ C, chi r b.val) * (∑ c ∈ D, chi r c.val)
              = (∑ a ∈ B, ∑ b ∈ C, chi r a.val * chi r b.val) * (∑ c ∈ D, chi r c.val) := by
                rw [Finset.sum_mul]; refine congrArg (· * _) (Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _)
            _ = ∑ a ∈ B, (∑ b ∈ C, chi r a.val * chi r b.val) * (∑ c ∈ D, chi r c.val) :=
                Finset.sum_mul _ _ _
            _ = ∑ a ∈ B, ∑ b ∈ C, (chi r a.val * chi r b.val) * (∑ c ∈ D, chi r c.val) :=
                Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
            _ = ∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, chi r (a.val + b.val + c.val) := by
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun c _ => by rw [chi_add_right, chi_add_right]
        rw [div_mul_div_comm, div_mul_div_comm, hnum]
        ring
      simp_rw [hmul, ← Finset.sum_div]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    rw [hexp]
    have hcount : ∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, ∑ r : 𝔽₂ n, chi r (a.val + b.val + c.val) =
        (((B ×ˢ C ×ˢ D).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) *
        (Fintype.card (𝔽₂ n) : ℝ) := by
      simp_rw [sum_chi_over_dual]
      have hcard : (((B ×ˢ C ×ˢ D).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) =
          ∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, if a.val + b.val + c.val = 0 then (1 : ℝ) else 0 := by
        have hnat : ((B ×ˢ C ×ˢ D).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card =
            ∑ a ∈ B, ∑ b ∈ C, ∑ c ∈ D, if a.val + b.val + c.val = 0 then 1 else 0 := by
          rw [Finset.card_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          have hiff : (a + b + c = 0) ↔ (a.val + b.val + c.val = 0) := by
            simp [Subtype.ext_iff]
          simp [hiff]
        exact_mod_cast hnat
      rw [hcard, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
    rw [hcount, ← card_ann_mul_card_subspace W]
    field_simp [hW_pos.ne']
  -- Split ∑ r into ann W and univ \ ann W.
  have hsplit : ∑ r : 𝔽₂ n, fhat W B r * fhat W C r * fhat W D r =
      (∑ r ∈ ann W, fhat W B r * fhat W C r * fhat W D r) +
      (∑ r ∈ univ \ ann W, fhat W B r * fhat W C r * fhat W D r) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hmain : ∑ r ∈ ann W, fhat W B r * fhat W C r * fhat W D r =
      ((ann W).card : ℝ) *
      (((B.card : ℝ) / (Fintype.card W : ℝ)) *
       ((C.card : ℝ) / (Fintype.card W : ℝ)) *
       ((D.card : ℝ) / (Fintype.card W : ℝ))) := by
    have hcongr : ∀ r ∈ ann W, fhat W B r * fhat W C r * fhat W D r =
        ((B.card : ℝ) / (Fintype.card W : ℝ)) *
        ((C.card : ℝ) / (Fintype.card W : ℝ)) *
        ((D.card : ℝ) / (Fintype.card W : ℝ)) := fun r hr => by
      rw [fhat_of_mem_ann W B hr, fhat_of_mem_ann W C hr, fhat_of_mem_ann W D hr]
    rw [Finset.sum_congr rfl hcongr]
    simp
  have herr : ∑ r ∈ univ \ ann W, fhat W B r * fhat W C r * fhat W D r ≤
      ((ann W).card : ℝ) * η := by
    calc ∑ r ∈ univ \ ann W, fhat W B r * fhat W C r * fhat W D r
        ≤ ∑ r ∈ univ \ ann W, |fhat W B r * fhat W C r * fhat W D r| :=
          sum_le_sum fun r _ => le_abs_self _
      _ ≤ ∑ r ∈ univ \ ann W, η * (((fhat W C r) ^ 2 + (fhat W D r) ^ 2) / 2) := by
          refine sum_le_sum fun r hr => ?_
          have hrnot : r ∉ ann W := (Finset.mem_sdiff.mp hr).2
          have hB : |fhat W B r| ≤ η := hunif r hrnot
          have ham : |fhat W C r| * |fhat W D r| ≤ ((fhat W C r) ^ 2 + (fhat W D r) ^ 2) / 2 := by
            have hsq : 0 ≤ (|fhat W C r| - |fhat W D r|) ^ 2 := sq_nonneg _
            have hc : |fhat W C r| ^ 2 = (fhat W C r) ^ 2 := sq_abs _
            have hd : |fhat W D r| ^ 2 = (fhat W D r) ^ 2 := sq_abs _
            nlinarith
          calc |fhat W B r * fhat W C r * fhat W D r|
              = |fhat W B r| * (|fhat W C r| * |fhat W D r|) := by
                rw [abs_mul, abs_mul, mul_assoc]
            _ ≤ η * (((fhat W C r) ^ 2 + (fhat W D r) ^ 2) / 2) :=
                mul_le_mul hB ham (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hη
      _ ≤ ∑ r : 𝔽₂ n, η * (((fhat W C r) ^ 2 + (fhat W D r) ^ 2) / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ => by positivity
      _ = η * ((∑ r : 𝔽₂ n, (fhat W C r) ^ 2 + ∑ r : 𝔽₂ n, (fhat W D r) ^ 2) / 2) := by
          simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
      _ = η * (((ann W).card : ℝ) * (((C.card : ℝ) / (Fintype.card W : ℝ) +
            (D.card : ℝ) / (Fintype.card W : ℝ)) / 2)) := by
          rw [parseval_subspace W C, parseval_subspace W D]; ring
      _ ≤ η * (((ann W).card : ℝ) * 1) := by
          have hC1 : (C.card : ℝ) / (Fintype.card W : ℝ) ≤ 1 := by
            rw [div_le_one hW_pos]
            exact_mod_cast Finset.card_le_univ C
          have hD1 : (D.card : ℝ) / (Fintype.card W : ℝ) ≤ 1 := by
            rw [div_le_one hW_pos]
            exact_mod_cast Finset.card_le_univ D
          have havg : ((C.card : ℝ) / (Fintype.card W : ℝ) +
              (D.card : ℝ) / (Fintype.card W : ℝ)) / 2 ≤ 1 := by linarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left havg hann_pos.le) hη
      _ = ((ann W).card : ℝ) * η := by ring
  have htot : ((ann W).card : ℝ) *
      ((((B ×ˢ C ×ˢ D).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) /
        (Fintype.card W : ℝ) ^ 2) ≤
      ((ann W).card : ℝ) *
      (((B.card : ℝ) / (Fintype.card W : ℝ)) *
       ((C.card : ℝ) / (Fintype.card W : ℝ)) *
       ((D.card : ℝ) / (Fintype.card W : ℝ)) + η) := by
    linarith
  exact le_of_mul_le_mul_left htot hann_pos

/-- Index-2 kernel split: splitting `W` by `dot r · = 0` increments `δ(S)^2` by `(fhat W S r)^2`. -/
private lemma kernel_split_energy {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n))
    (S : Finset W) {r : 𝔽₂ n} (hr : r ∉ ann W) :
    let φ : W → ZMod 2 := fun w => dot r w.val
    (Fintype.card W : ℝ) * ((S.card : ℝ) / (Fintype.card W : ℝ)) ^ 2 +
    (Fintype.card W : ℝ) * (fhat W S r) ^ 2 =
    ∑ b : ZMod 2, ((univ.filter (fun w : W => φ w = b)).card : ℝ) *
      (setDens (univ.filter (fun w : W => φ w = b)) S) ^ 2 := by
  intro φ
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  simp only [ann, mem_filter, mem_univ, true_and, not_forall] at hr
  rcases hr with ⟨w₀, hw₀⟩
  have hφ0 : dot r w₀.val = 1 := by
    rcases zmod2_eq_zero_or_one (dot r w₀.val) with h | h
    · exact absurd h hw₀
    · exact h
  -- Both fibers `φ = 0` and `φ = 1` have cardinality `|W| / 2`.
  let W0 : Finset W := univ.filter (fun w : W => φ w = 0)
  let W1 : Finset W := univ.filter (fun w : W => φ w = 1)
  have hcard_eq : W0.card = W1.card := by
    refine Finset.card_bij (fun w _ => w + w₀) ?_ ?_ ?_
    · intro w hw
      simp only [W0, W1, φ, mem_filter, mem_univ, true_and, Submodule.coe_add, dot_add_right] at hw ⊢
      rw [hw, hφ0]; decide
    · intro w₁ _ w₂ _ h
      exact add_right_cancel h
    · intro w hw
      refine ⟨w + w₀, ?_, ?_⟩
      · simp only [W0, W1, φ, mem_filter, mem_univ, true_and, Submodule.coe_add, dot_add_right] at hw ⊢
        rw [hw, hφ0]; decide
      · apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [add_assoc, f2_add_self, add_zero]
  have hcard_sum : W0.card + W1.card = Fintype.card W := by
    have hdisj : Disjoint W0 W1 := by
      rw [Finset.disjoint_filter]
      intro w _ h0 h1; rw [h0] at h1; exact zero_ne_one h1
    have hunion : W0 ∪ W1 = univ := by
      ext w
      simp only [W0, W1, mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact zmod2_eq_zero_or_one (φ w)
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have hW0_card : (W0.card : ℝ) = (Fintype.card W : ℝ) / 2 := by
    have : 2 * W0.card = Fintype.card W := by omega
    have : (2 : ℝ) * (W0.card : ℝ) = (Fintype.card W : ℝ) := by exact_mod_cast this
    linarith
  have hW1_card : (W1.card : ℝ) = (Fintype.card W : ℝ) / 2 := by
    have : (W0.card : ℝ) = (W1.card : ℝ) := by exact_mod_cast hcard_eq
    linarith
  -- Express fhat W S r as (d0 - d1) / 2 and δ(S) as (d0 + d1) / 2.
  set d0 := setDens W0 S
  set d1 := setDens W1 S
  have hS0 : ((S ∩ W0).card : ℝ) = (Fintype.card W : ℝ) / 2 * d0 := by
    rw [← hW0_card, card_mul_setDens]
  have hS1 : ((S ∩ W1).card : ℝ) = (Fintype.card W : ℝ) / 2 * d1 := by
    rw [← hW1_card, card_mul_setDens]
  have hdisjS : Disjoint (S ∩ W0) (S ∩ W1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    simp only [mem_inter, W0, W1, mem_filter, mem_univ, true_and] at h0 h1
    rw [h0.2] at h1; exact zero_ne_one h1.2
  have hunionS : (S ∩ W0) ∪ (S ∩ W1) = S := by
    ext w
    simp only [mem_union, mem_inter, W0, W1, mem_filter, mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases zmod2_eq_zero_or_one (φ w) with hp | hp
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hp⟩
  have hS_split : (S.card : ℝ) = ((S ∩ W0).card : ℝ) + ((S ∩ W1).card : ℝ) := by
    have hnat : (S ∩ W0).card + (S ∩ W1).card = S.card := by
      rw [← Finset.card_union_of_disjoint hdisjS, hunionS]
    exact_mod_cast hnat.symm
  have hfhat_eq : fhat W S r = (d0 - d1) / 2 := by
    unfold fhat
    have hsum : ∑ w ∈ S, chi r w.val = ((S ∩ W0).card : ℝ) - ((S ∩ W1).card : ℝ) := by
      conv_lhs => rw [← hunionS]
      rw [Finset.sum_union hdisjS]
      have h0 : ∀ w ∈ S ∩ W0, chi r w.val = 1 := fun w hw => by
        simp only [mem_inter, W0, φ, mem_filter, mem_univ, true_and] at hw
        simp [chi, hw.2]
      have h1 : ∀ w ∈ S ∩ W1, chi r w.val = -1 := fun w hw => by
        simp only [mem_inter, W1, φ, mem_filter, mem_univ, true_and] at hw
        simp [chi, hw.2]
      rw [Finset.sum_congr rfl h0, Finset.sum_congr rfl h1]
      simp [sub_eq_add_neg]
    rw [hsum, hS0, hS1]
    field_simp [hW_pos.ne']
  have hδ_eq : (S.card : ℝ) / (Fintype.card W : ℝ) = (d0 + d1) / 2 := by
    rw [hS_split, hS0, hS1]
    field_simp [hW_pos.ne']
  have hsum_zmod : ∑ b : ZMod 2, ((univ.filter (fun w : W => φ w = b)).card : ℝ) *
      (setDens (univ.filter (fun w : W => φ w = b)) S) ^ 2 =
      (W0.card : ℝ) * d0 ^ 2 + (W1.card : ℝ) * d1 ^ 2 := by
    rw [sum_zmod2]
  rw [hsum_zmod, hW0_card, hW1_card, hδ_eq, hfhat_eq]
  ring

end Fourier

/- ## Section 4: Mandache Regularity Lemma on `𝔽₂ n` -/

section Regularity

/-- Index set of outer boxes for a subspace `W ≤ 𝔽₂ n`. -/
private abbrev Q {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) := (𝔽₂ n ⧸ W) × (𝔽₂ n ⧸ W)

/-- Chosen coset representative for `q : 𝔽₂ n ⧸ W`. -/
private noncomputable def rep {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) (q : 𝔽₂ n ⧸ W) : 𝔽₂ n :=
  Quotient.out q

private lemma mk_rep {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) (q : 𝔽₂ n ⧸ W) :
    Submodule.Quotient.mk (p := W) (rep W q) = q :=
  Quotient.out_eq q

private lemma quot_add_self {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) (q : 𝔽₂ n ⧸ W) :
    q + q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk (p := W) (x + x) = Submodule.Quotient.mk (p := W) 0
    rw [f2_add_self]

private lemma add_rep_mem {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) (x : 𝔽₂ n) :
    x + rep W (Submodule.Quotient.mk (p := W) x) ∈ W := by
  rw [← Submodule.Quotient.mk_eq_zero]
  change Submodule.Quotient.mk (p := W) x + Submodule.Quotient.mk (p := W) (rep W _) = 0
  rw [mk_rep, quot_add_self]

/-- A boxing of `𝔽₂ n`: a subspace `W`, a positive number `m` of parts, and three `m`-colorings
of `W` for each outer box `q ∈ (𝔽₂ n ⧸ W)²`. -/
private structure Boxing (n : ℕ) where
  W : Submodule (ZMod 2) (𝔽₂ n)
  m : ℕ
  hm : 0 < m
  labB : Q W → W → Fin m
  labC : Q W → W → Fin m
  labD : Q W → W → Fin m

private noncomputable def A_box {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) (q : Q W) : Finset (W × W) :=
  univ.filter (fun p : W × W => (rep W q.1 + p.1.val, rep W q.2 + p.2.val) ∈ A)

private def eBC {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (W : Submodule (ZMod 2) (𝔽₂ n))
    (q : Q W) (a b : W) : Prop :=
  (a, b) ∈ A_box A W q

private def eBD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (W : Submodule (ZMod 2) (𝔽₂ n))
    (q : Q W) (a c : W) : Prop :=
  (a, a + c) ∈ A_box A W q

private def eCD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (W : Submodule (ZMod 2) (𝔽₂ n))
    (q : Q W) (b c : W) : Prop :=
  (b + c, b) ∈ A_box A W q

private noncomputable def Bset {n : ℕ} (B : Boxing n) (q : Q B.W) (i : Fin B.m) : Finset B.W :=
  univ.filter (fun w => B.labB q w = i)

private noncomputable def Cset {n : ℕ} (B : Boxing n) (q : Q B.W) (j : Fin B.m) : Finset B.W :=
  univ.filter (fun w => B.labC q w = j)

private noncomputable def Dset {n : ℕ} (B : Boxing n) (q : Q B.W) (k : Fin B.m) : Finset B.W :=
  univ.filter (fun w => B.labD q w = k)

private noncomputable def δ₁ {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} (S : Finset W) : ℝ :=
  (S.card : ℝ) / (Fintype.card W : ℝ)

private lemma δ₁_nonneg {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} (S : Finset W) : 0 ≤ δ₁ S := by
  unfold δ₁; positivity

private lemma δ₁_le_one {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} (S : Finset W) : δ₁ S ≤ 1 := by
  unfold δ₁
  rw [div_le_one (Nat.cast_pos.mpr Fintype.card_pos)]
  exact_mod_cast Finset.card_le_univ S

private lemma sum_δ₁_label {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} {m : ℕ} (lab : W → Fin m) :
    ∑ i : Fin m, δ₁ (univ.filter (fun w : W => lab w = i)) = 1 := by
  unfold δ₁
  rw [← Finset.sum_div]
  have hsum : ∑ i : Fin m, ((univ.filter (fun w : W => lab w = i)).card : ℝ) =
      (Fintype.card W : ℝ) := by
    have hnat : ∑ i : Fin m, (univ.filter (fun w : W => lab w = i)).card = Fintype.card W := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      simp
    exact_mod_cast hnat
  rw [hsum, div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

private lemma sum_δ₁_sq_le_one {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} {m : ℕ} (lab : W → Fin m) :
    ∑ i : Fin m, (δ₁ (univ.filter (fun w : W => lab w = i))) ^ 2 ≤ 1 := by
  calc ∑ i : Fin m, (δ₁ (univ.filter (fun w : W => lab w = i))) ^ 2
      ≤ ∑ i : Fin m, δ₁ (univ.filter (fun w : W => lab w = i)) := by
        refine sum_le_sum fun i _ => ?_
        have h0 := δ₁_nonneg (univ.filter (fun w : W => lab w = i))
        have h1 := δ₁_le_one (univ.filter (fun w : W => lab w = i))
        nlinarith
    _ = 1 := sum_δ₁_label lab

private noncomputable def innerTerm {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (X Y : Finset W) (e : W → W → Prop) : ℝ :=
  δ₁ X * δ₁ Y * (edgeDens X Y e) ^ 2

private lemma innerTerm_nonneg {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (X Y : Finset W) (e : W → W → Prop) : 0 ≤ innerTerm X Y e := by
  unfold innerTerm; exact mul_nonneg (mul_nonneg (δ₁_nonneg X) (δ₁_nonneg Y)) (sq_nonneg _)

private lemma innerTerm_eq_setDens {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)}
    (X Y : Finset W) (e : W → W → Prop) :
    innerTerm X Y e =
      (((X ×ˢ Y).card : ℝ) * (setDens (X ×ˢ Y) (univ.filter (fun p : W × W => e p.1 p.2))) ^ 2) /
      (Fintype.card W : ℝ) ^ 2 := by
  have hsd : edgeDens X Y e = setDens (X ×ˢ Y) (univ.filter (fun p : W × W => e p.1 p.2)) := by
    rw [edgeDens_eq_setDens]
    unfold setDens
    have hinter : (X ×ˢ Y).filter (fun p => e p.1 p.2) ∩ (X ×ˢ Y) =
        univ.filter (fun p : W × W => e p.1 p.2) ∩ (X ×ˢ Y) := by
      ext p; simp [and_comm]
    rw [hinter]
  unfold innerTerm δ₁
  rw [hsd, Finset.card_product, Nat.cast_mul]
  ring

private noncomputable def E₁_box {n : ℕ} (B : Boxing n) (q : Q B.W) : ℝ :=
  (∑ i : Fin B.m, ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 + (δ₁ (Dset B q i)) ^ 2)) / 3

private noncomputable def E₁ {n : ℕ} (B : Boxing n) : ℝ :=
  (∑ q : Q B.W, E₁_box B q) / (Fintype.card (Q B.W) : ℝ)

private noncomputable def E₂_box {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : ℝ :=
  (∑ i : Fin B.m, ∑ j : Fin B.m,
    (innerTerm (Bset B q i) (Cset B q j) (eBC A B.W q) +
     innerTerm (Bset B q i) (Dset B q j) (eBD A B.W q) +
     innerTerm (Cset B q i) (Dset B q j) (eCD A B.W q))) / 3

private noncomputable def E₂ {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) : ℝ :=
  (∑ q : Q B.W, E₂_box A B q) / (Fintype.card (Q B.W) : ℝ)

private lemma E₁_nonneg {n : ℕ} (B : Boxing n) : 0 ≤ E₁ B := by
  unfold E₁ E₁_box
  refine div_nonneg (sum_nonneg fun q _ => div_nonneg (sum_nonneg fun i _ => ?_) (by norm_num))
    (Nat.cast_nonneg _)
  positivity

private lemma E₁_le_one {n : ℕ} (B : Boxing n) : E₁ B ≤ 1 := by
  have hQ : (0 : ℝ) < (Fintype.card (Q B.W) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  unfold E₁
  rw [div_le_one hQ]
  calc ∑ q : Q B.W, E₁_box B q
      ≤ ∑ _q : Q B.W, (1 : ℝ) := by
        refine sum_le_sum fun q _ => ?_
        unfold E₁_box Bset Cset Dset
        simp only [Finset.sum_add_distrib]
        have hB := sum_δ₁_sq_le_one (B.labB q)
        have hC := sum_δ₁_sq_le_one (B.labC q)
        have hD := sum_δ₁_sq_le_one (B.labD q)
        linarith
    _ = (Fintype.card (Q B.W) : ℝ) := by simp

private lemma E₂_nonneg {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) : 0 ≤ E₂ A B := by
  unfold E₂ E₂_box
  refine div_nonneg (sum_nonneg fun q _ => div_nonneg (sum_nonneg fun i _ => sum_nonneg fun j _ => ?_)
    (by norm_num)) (Nat.cast_nonneg _)
  exact add_nonneg (add_nonneg (innerTerm_nonneg _ _ _) (innerTerm_nonneg _ _ _))
    (innerTerm_nonneg _ _ _)

private lemma sum_innerTerm_le_one {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} {m : ℕ}
    (lab1 lab2 : W → Fin m) (e : W → W → Prop) :
    ∑ i : Fin m, ∑ j : Fin m,
      innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e ≤ 1 := by
  calc ∑ i : Fin m, ∑ j : Fin m,
        innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e
      ≤ ∑ i : Fin m, ∑ j : Fin m,
          δ₁ (univ.filter (fun w => lab1 w = i)) * δ₁ (univ.filter (fun w => lab2 w = j)) := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        unfold innerTerm
        have hd0 := edgeDens_nonneg (univ.filter (fun w => lab1 w = i))
          (univ.filter (fun w => lab2 w = j)) e
        have hd1 := edgeDens_le_one (univ.filter (fun w => lab1 w = i))
          (univ.filter (fun w => lab2 w = j)) e
        have hsq : (edgeDens (univ.filter (fun w => lab1 w = i))
            (univ.filter (fun w => lab2 w = j)) e) ^ 2 ≤ 1 := by nlinarith
        have hprod : 0 ≤ δ₁ (univ.filter (fun w => lab1 w = i)) *
            δ₁ (univ.filter (fun w => lab2 w = j)) :=
          mul_nonneg (δ₁_nonneg _) (δ₁_nonneg _)
        nlinarith
    _ = (∑ i : Fin m, δ₁ (univ.filter (fun w => lab1 w = i))) *
        (∑ j : Fin m, δ₁ (univ.filter (fun w => lab2 w = j))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = 1 := by rw [sum_δ₁_label lab1, sum_δ₁_label lab2, mul_one]

private lemma E₂_le_one {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) : E₂ A B ≤ 1 := by
  have hQ : (0 : ℝ) < (Fintype.card (Q B.W) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  unfold E₂
  rw [div_le_one hQ]
  calc ∑ q : Q B.W, E₂_box A B q
      ≤ ∑ _q : Q B.W, (1 : ℝ) := by
        refine sum_le_sum fun q _ => ?_
        unfold E₂_box Bset Cset Dset
        simp only [Finset.sum_add_distrib]
        have hBC := sum_innerTerm_le_one (B.labB q) (B.labC q) (eBC A B.W q)
        have hBD := sum_innerTerm_le_one (B.labB q) (B.labD q) (eBD A B.W q)
        have hCD := sum_innerTerm_le_one (B.labC q) (B.labD q) (eCD A B.W q)
        linarith
    _ = (Fintype.card (Q B.W) : ℝ) := by simp

/-- Regularity condition (1) for a single outer box `q`. -/
private def BoxUnif {n : ℕ} (ε : ℝ) (B : Boxing n) (q : Q B.W) : Prop :=
  ∀ i : Fin B.m, ∀ r : 𝔽₂ n, r ∉ ann B.W →
    |fhat B.W (Bset B q i) r| ≤ ε / (B.m : ℝ) ^ 3 ∧
    |fhat B.W (Cset B q i) r| ≤ ε / (B.m : ℝ) ^ 3 ∧
    |fhat B.W (Dset B q i) r| ≤ ε / (B.m : ℝ) ^ 3

/-- Regularity condition (1) for a boxing. -/
private def Cond1 {n : ℕ} (ε : ℝ) (B : Boxing n) : Prop :=
  ((univ.filter (fun q : Q B.W => ¬ BoxUnif ε B q)).card : ℝ) ≤ ε * (Fintype.card (Q B.W) : ℝ)

private noncomputable def badBC {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : ℝ :=
  ∑ i : Fin B.m, ∑ j : Fin B.m,
    if IsQuasirandom ε (Bset B q i) (Cset B q j) (eBC A B.W q) then 0
    else δ₁ (Bset B q i) * δ₁ (Cset B q j)

private noncomputable def badBD {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : ℝ :=
  ∑ i : Fin B.m, ∑ j : Fin B.m,
    if IsQuasirandom ε (Bset B q i) (Dset B q j) (eBD A B.W q) then 0
    else δ₁ (Bset B q i) * δ₁ (Dset B q j)

private noncomputable def badCD {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : ℝ :=
  ∑ i : Fin B.m, ∑ j : Fin B.m,
    if IsQuasirandom ε (Cset B q i) (Dset B q j) (eCD A B.W q) then 0
    else δ₁ (Cset B q i) * δ₁ (Dset B q j)

private lemma badBC_nonneg {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : 0 ≤ badBC ε A B q :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (δ₁_nonneg _) (δ₁_nonneg _)

private lemma badBD_nonneg {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : 0 ≤ badBD ε A B q :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (δ₁_nonneg _) (δ₁_nonneg _)

private lemma badCD_nonneg {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n))
    (B : Boxing n) (q : Q B.W) : 0 ≤ badCD ε A B q :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (δ₁_nonneg _) (δ₁_nonneg _)

/-- Regularity condition (2) for a single outer box `q`. -/
private def BoxQR {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (q : Q B.W) : Prop :=
  badBC ε A B q ≤ ε ∧ badBD ε A B q ≤ ε ∧ badCD ε A B q ≤ ε

/-- Regularity condition (2) for a boxing. -/
private def Cond2 {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) : Prop :=
  ((univ.filter (fun q : Q B.W => ¬ BoxQR ε A B q)).card : ℝ) ≤ ε * (Fintype.card (Q B.W) : ℝ)

/-- An `ε`-regular boxing of `A`. -/
private def IsRegular {n : ℕ} (ε : ℝ) (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) : Prop :=
  Cond1 ε B ∧ Cond2 ε A B

/-- Codimension of a subspace `W ≤ 𝔽₂ n`. -/
private noncomputable def codim {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) : ℕ :=
  Module.finrank (ZMod 2) (𝔽₂ n ⧸ W)

private lemma card_quot_eq_two_pow_codim {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    Fintype.card (𝔽₂ n ⧸ W) = 2 ^ codim W := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := 𝔽₂ n ⧸ W)
  simpa [codim, ZMod.card] using h

private lemma card_subspace_eq_two_pow_finrank {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
  simpa [ZMod.card] using h

private lemma codim_add_finrank {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    codim W + Module.finrank (ZMod 2) W = n := by
  have h := Submodule.finrank_quotient_add_finrank W
  have hfn : Module.finrank (ZMod 2) (𝔽₂ n) = n := by
    simp [𝔽₂, 𝔽]
  unfold codim
  omega

private lemma card_quot_mul_card_subspace {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    Fintype.card (𝔽₂ n ⧸ W) * Fintype.card W = Fintype.card (𝔽₂ n) := by
  rw [card_quot_eq_two_pow_codim, card_subspace_eq_two_pow_finrank, ← pow_add, codim_add_finrank]
  simp [𝔽₂, 𝔽, ZMod.card]

private lemma card_Q_eq_four_pow_codim {n : ℕ} (W : Submodule (ZMod 2) (𝔽₂ n)) :
    Fintype.card (Q W) = 4 ^ codim W := by
  rw [Fintype.card_prod, card_quot_eq_two_pow_codim, ← mul_pow]
  norm_num

/- ### Subspace restriction machinery for Refinement (A) -/

private lemma factor_mk' {n : ℕ} {T W : Submodule (ZMod 2) (𝔽₂ n)} (hTW : T ≤ W) (x : 𝔽₂ n) :
    Submodule.factor hTW (Submodule.Quotient.mk (p := T) x) = Submodule.Quotient.mk (p := W) x :=
  Submodule.factor_mk hTW x

/-- Shift element `rep T r₁ + rep W (factor hTW r₁) ∈ W`. -/
private noncomputable def shiftW {n : ℕ} {T W : Submodule (ZMod 2) (𝔽₂ n)} (hTW : T ≤ W)
    (r₁ : 𝔽₂ n ⧸ T) : W :=
  ⟨rep T r₁ + rep W (Submodule.factor hTW r₁), by
    rw [← Submodule.Quotient.mk_eq_zero]
    change Submodule.Quotient.mk (p := W) (rep T r₁) +
      Submodule.Quotient.mk (p := W) (rep W (Submodule.factor hTW r₁)) = 0
    have h1 : Submodule.Quotient.mk (p := W) (rep T r₁) = Submodule.factor hTW r₁ := by
      have hm := factor_mk' hTW (rep T r₁)
      rw [mk_rep] at hm
      exact hm.symm
    rw [h1, mk_rep, quot_add_self]⟩

private noncomputable def fiberQ {n : ℕ} {T W : Submodule (ZMod 2) (𝔽₂ n)} (hTW : T ≤ W)
    (q₁ : 𝔽₂ n ⧸ W) : Finset (𝔽₂ n ⧸ T) :=
  univ.filter (fun r₁ => Submodule.factor hTW r₁ = q₁)

private lemma card_fiberQ_mul {n : ℕ} {T W : Submodule (ZMod 2) (𝔽₂ n)} (hTW : T ≤ W)
    (q₁ : 𝔽₂ n ⧸ W) :
    (fiberQ hTW q₁).card * Fintype.card T = Fintype.card W := by
  have hbij : ((fiberQ hTW q₁) ×ˢ (univ : Finset T)).card = (univ : Finset W).card := by
    refine Finset.card_bij
      (fun p _ => shiftW hTW p.1 + (⟨p.2.val, hTW p.2.prop⟩ : W)) ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and] at hp₁ hp₂
      have hval : rep T p₁.1 + rep W q₁ + p₁.2.val = rep T p₂.1 + rep W q₁ + p₂.2.val := by
        have := congrArg Subtype.val heq
        simpa [shiftW, hp₁, hp₂] using this
      have hmk : Submodule.Quotient.mk (p := T) (rep T p₁.1 + rep W q₁ + p₁.2.val) =
          Submodule.Quotient.mk (p := T) (rep T p₂.1 + rep W q₁ + p₂.2.val) :=
        congrArg _ hval
      have hmk1 : Submodule.Quotient.mk (p := T) (rep T p₁.1 + rep W q₁ + p₁.2.val) =
          p₁.1 + Submodule.Quotient.mk (p := T) (rep W q₁) := by
        change (Submodule.Quotient.mk (p := T) (rep T p₁.1) +
          Submodule.Quotient.mk (p := T) (rep W q₁)) +
          Submodule.Quotient.mk (p := T) p₁.2.val = _
        rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr p₁.2.prop, add_zero]
      have hmk2 : Submodule.Quotient.mk (p := T) (rep T p₂.1 + rep W q₁ + p₂.2.val) =
          p₂.1 + Submodule.Quotient.mk (p := T) (rep W q₁) := by
        change (Submodule.Quotient.mk (p := T) (rep T p₂.1) +
          Submodule.Quotient.mk (p := T) (rep W q₁)) +
          Submodule.Quotient.mk (p := T) p₂.2.val = _
        rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr p₂.2.prop, add_zero]
      rw [hmk1, hmk2] at hmk
      have hr : p₁.1 = p₂.1 := add_right_cancel hmk
      have ht : p₁.2 = p₂.2 := by
        apply Subtype.ext
        rw [hr] at hval
        exact add_left_cancel hval
      exact Prod.ext hr ht
    · intro w _
      let x : 𝔽₂ n := rep W q₁ + w.val
      let r₁ : 𝔽₂ n ⧸ T := Submodule.Quotient.mk (p := T) x
      let t : T := ⟨x + rep T r₁, add_rep_mem T x⟩
      have hr₁ : Submodule.factor hTW r₁ = q₁ := by
        dsimp only [r₁, x]
        rw [factor_mk' hTW]
        change Submodule.Quotient.mk (p := W) (rep W q₁) +
          Submodule.Quotient.mk (p := W) w.val = q₁
        rw [mk_rep, (Submodule.Quotient.mk_eq_zero W).mpr w.prop, add_zero]
      refine ⟨(r₁, t), ?_, ?_⟩
      · simp [fiberQ, hr₁]
      · apply Subtype.ext
        simp only [Submodule.coe_add, shiftW, hr₁, t, x]
        calc rep T r₁ + rep W q₁ + (rep W q₁ + w.val + rep T r₁)
            = (rep T r₁ + rep T r₁) + (rep W q₁ + rep W q₁) + w.val := by abel
          _ = w.val := by simp only [f2_add_self, zero_add]
  rw [Finset.card_product, Finset.card_univ, Finset.card_univ] at hbij
  exact hbij

/-- Core lemma for `E₁` under subspace restriction: translating by `x₀` and slicing into `T`-cosets
never decreases `δ₁(S)^2`, and increments by `(fhat W S r)^2` whenever `T ≤ ker (dotLM r)`. -/
private lemma coset_slice_energy_bound {n : ℕ} {T W : Submodule (ZMod 2) (𝔽₂ n)} (hTW : T ≤ W)
    (q₁ : 𝔽₂ n ⧸ W) (u : W) (S : Finset W) :
    let K : ℝ := (fiberQ hTW q₁).card
    let slice : (𝔽₂ n ⧸ T) → Finset T := fun r₁ =>
      univ.filter (fun t : T => u + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩ ∈ S)
    (δ₁ S) ^ 2 ≤ (∑ r₁ ∈ fiberQ hTW q₁, (δ₁ (slice r₁)) ^ 2) / K ∧
    ∀ r : 𝔽₂ n, r ∉ ann W → (∀ t : T, dot r t.val = 0) →
      (δ₁ S) ^ 2 + (fhat W S r) ^ 2 ≤ (∑ r₁ ∈ fiberQ hTW q₁, (δ₁ (slice r₁)) ^ 2) / K := by
  intro K slice
  have hKmul : K * (Fintype.card T : ℝ) = (Fintype.card W : ℝ) := by
    dsimp only [K]; exact_mod_cast card_fiberQ_mul hTW q₁
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hT_pos : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hK_pos : 0 < K := by nlinarith
  -- Label map ψ : W → 𝔽₂ n ⧸ T sending w ↦ mk_T (rep W q₁ + u + w).
  let ψ : W → (𝔽₂ n ⧸ T) := fun w => Submodule.Quotient.mk (p := T) (rep W q₁ + u.val + w.val)
  -- For r₁ ∈ fiberQ hTW q₁, the fiber {w : W | ψ w = r₁} has card |T| and density δ₁ (slice r₁).
  have hfiber_eq : ∀ r₁ ∈ fiberQ hTW q₁,
      ((univ.filter (fun w : W => ψ w = r₁)).card : ℝ) *
        (setDens (univ.filter (fun w : W => ψ w = r₁)) S) ^ 2 =
      (Fintype.card T : ℝ) * (δ₁ (slice r₁)) ^ 2 := by
    intro r₁ hr₁
    simp only [fiberQ, mem_filter, mem_univ, true_and] at hr₁
    have hcard_f : (univ.filter (fun w : W => ψ w = r₁)).card = Fintype.card T := by
      have hbij : (univ.filter (fun w : W => ψ w = r₁)).card = (univ : Finset T).card := by
        refine Finset.card_bij
          (fun w hw => ⟨rep W q₁ + u.val + w.val + rep T r₁, by
            simp only [mem_filter, mem_univ, true_and, ψ] at hw
            rw [← hw]
            exact add_rep_mem T _⟩) ?_ ?_ ?_
        · intro w _; exact mem_univ _
        · intro w₁ _ w₂ _ h
          have hv : rep W q₁ + u.val + w₁.val + rep T r₁ = rep W q₁ + u.val + w₂.val + rep T r₁ :=
            congrArg Subtype.val h
          exact Subtype.ext (add_left_cancel (add_right_cancel hv))
        · intro t _
          refine ⟨u + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩, ?_, ?_⟩
          · simp only [mem_filter, mem_univ, true_and, ψ, Submodule.coe_add, shiftW, hr₁]
            have hsimp : rep W q₁ + u.val + (u.val + (rep T r₁ + rep W q₁) + t.val) =
                rep T r₁ + t.val := by
              calc rep W q₁ + u.val + (u.val + (rep T r₁ + rep W q₁) + t.val)
                  = (rep W q₁ + rep W q₁) + (u.val + u.val) + rep T r₁ + t.val := by abel
                _ = rep T r₁ + t.val := by simp only [f2_add_self, zero_add]
            rw [hsimp]
            change Submodule.Quotient.mk (p := T) (rep T r₁) +
              Submodule.Quotient.mk (p := T) t.val = r₁
            rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr t.prop, add_zero]
          · apply Subtype.ext
            simp only [Submodule.coe_add, shiftW, hr₁]
            calc rep W q₁ + u.val + (u.val + (rep T r₁ + rep W q₁) + t.val) + rep T r₁
                = (rep W q₁ + rep W q₁) + (u.val + u.val) + (rep T r₁ + rep T r₁) + t.val := by abel
              _ = t.val := by simp only [f2_add_self, zero_add]
      rw [hbij, Finset.card_univ]
    have hcard_inter : (S ∩ univ.filter (fun w : W => ψ w = r₁)).card = (slice r₁).card := by
      refine Finset.card_bij
        (fun w hw => ⟨rep W q₁ + u.val + w.val + rep T r₁, by
          simp only [mem_inter, mem_filter, mem_univ, true_and, ψ] at hw
          rw [← hw.2]; exact add_rep_mem T _⟩) ?_ ?_ ?_
      · intro w hw
        simp only [mem_inter, mem_filter, mem_univ, true_and, ψ] at hw
        simp only [slice, mem_filter, mem_univ, true_and]
        have hEq : u + shiftW hTW r₁ +
            ⟨rep W q₁ + u.val + w.val + rep T r₁, hTW (by rw [← hw.2]; exact add_rep_mem T _)⟩ = w := by
          apply Subtype.ext
          simp only [Submodule.coe_add, shiftW, hr₁]
          calc u.val + (rep T r₁ + rep W q₁) + (rep W q₁ + u.val + w.val + rep T r₁)
              = (u.val + u.val) + (rep T r₁ + rep T r₁) + (rep W q₁ + rep W q₁) + w.val := by abel
            _ = w.val := by simp only [f2_add_self, zero_add]
        rw [hEq]
        exact hw.1
      · intro w₁ _ w₂ _ h
        have hv : rep W q₁ + u.val + w₁.val + rep T r₁ = rep W q₁ + u.val + w₂.val + rep T r₁ :=
          congrArg Subtype.val h
        exact Subtype.ext (add_left_cancel (add_right_cancel hv))
      · intro t ht
        simp only [slice, mem_filter, mem_univ, true_and] at ht
        refine ⟨u + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩, ?_, ?_⟩
        · simp only [mem_inter, mem_filter, mem_univ, true_and]
          refine ⟨ht, ?_⟩
          dsimp only [ψ]
          simp only [Submodule.coe_add, shiftW, hr₁]
          have hsimp : rep W q₁ + u.val + (u.val + (rep T r₁ + rep W q₁) + t.val) =
              rep T r₁ + t.val := by
            calc rep W q₁ + u.val + (u.val + (rep T r₁ + rep W q₁) + t.val)
                = (rep W q₁ + rep W q₁) + (u.val + u.val) + rep T r₁ + t.val := by abel
              _ = rep T r₁ + t.val := by simp only [f2_add_self, zero_add]
          rw [hsimp]
          change Submodule.Quotient.mk (p := T) (rep T r₁) +
            Submodule.Quotient.mk (p := T) t.val = r₁
          rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr t.prop, add_zero]
        · apply Subtype.ext
          simp only [Submodule.coe_add, shiftW, hr₁]
          calc rep W q₁ + u.val + (u.val + (rep T r₁ + rep W q₁) + t.val) + rep T r₁
              = (rep W q₁ + rep W q₁) + (u.val + u.val) + (rep T r₁ + rep T r₁) + t.val := by abel
            _ = t.val := by simp only [f2_add_self, zero_add]
    have hdens : setDens (univ.filter (fun w : W => ψ w = r₁)) S = δ₁ (slice r₁) := by
      unfold setDens δ₁
      rw [hcard_f, hcard_inter]
      simp [Fintype.card_ne_zero]
    rw [hcard_f, hdens]
  -- Outside fiberQ hTW q₁, the fiber {w : W | ψ w = r₁} is empty.
  have hfiber_empty : ∀ r₁ : 𝔽₂ n ⧸ T, r₁ ∉ fiberQ hTW q₁ →
      univ.filter (fun w : W => ψ w = r₁) = ∅ := by
    intro r₁ hr₁
    ext w
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro hψ
    apply hr₁
    simp only [fiberQ, mem_filter, mem_univ, true_and, ← hψ, ψ]
    rw [factor_mk' hTW]
    change (Submodule.Quotient.mk (p := W) (rep W q₁) + Submodule.Quotient.mk (p := W) u.val) +
      Submodule.Quotient.mk (p := W) w.val = q₁
    rw [mk_rep, (Submodule.Quotient.mk_eq_zero W).mpr u.prop,
      (Submodule.Quotient.mk_eq_zero W).mpr w.prop, add_zero, add_zero]
  -- Total partition energy equals |T| * ∑ r₁ ∈ fiberQ, δ₁(slice r₁)^2.
  have hsum_eq : ∑ r₁ : 𝔽₂ n ⧸ T, ((univ.filter (fun w : W => ψ w = r₁)).card : ℝ) *
      (setDens (univ.filter (fun w : W => ψ w = r₁)) S) ^ 2 =
      (Fintype.card T : ℝ) * ∑ r₁ ∈ fiberQ hTW q₁, (δ₁ (slice r₁)) ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (fiberQ hTW q₁))]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hfiber_eq
    · intro r₁ _ hr₁
      rw [hfiber_empty r₁ hr₁]; simp
  have hsd_univ : setDens (univ : Finset W) S = δ₁ S := by
    unfold setDens δ₁
    simp [Fintype.card_ne_zero]
  constructor
  · have hmono := partition_energy_mono (univ : Finset W) S ψ
    rw [Finset.card_univ, hsd_univ, hsum_eq] at hmono
    rw [le_div_iff₀ hK_pos]
    nlinarith
  · intro r hr hTker
    have hker_le : T ≤ LinearMap.ker (dotLM r) := fun t ht => hTker ⟨t, ht⟩
    let liftR : (𝔽₂ n ⧸ T) →ₗ[ZMod 2] ZMod 2 := Submodule.liftQ T (dotLM r) hker_le
    let proj : (𝔽₂ n ⧸ T) → ZMod 2 := fun r₁ => liftR r₁ + dot r (rep W q₁ + u.val)
    have hproj : ∀ w ∈ (univ : Finset W), proj (ψ w) = dot r w.val := by
      intro w _
      dsimp only [proj, ψ, liftR]
      rw [Submodule.liftQ_apply]
      change dot r (rep W q₁ + u.val + w.val) + dot r (rep W q₁ + u.val) = dot r w.val
      rw [dot_add_right]
      have hcomm : dot r (rep W q₁ + u.val) + dot r w.val + dot r (rep W q₁ + u.val) =
          (dot r (rep W q₁ + u.val) + dot r (rep W q₁ + u.val)) + dot r w.val := by abel
      rw [hcomm, ← dot_add_right, f2_add_self, dot_zero_right, zero_add]
    have href := refinement_energy_mono (univ : Finset W) S (fun w : W => dot r w.val) ψ proj hproj
    have hker_eq : (Fintype.card W : ℝ) * (δ₁ S) ^ 2 + (Fintype.card W : ℝ) * (fhat W S r) ^ 2 =
        ∑ b : ZMod 2, ((univ.filter (fun w : W => dot r w.val = b)).card : ℝ) *
          (setDens (univ.filter (fun w : W => dot r w.val = b)) S) ^ 2 :=
      kernel_split_energy W S hr
    rw [hsum_eq] at href
    have hle : (Fintype.card W : ℝ) * (δ₁ S) ^ 2 + (Fintype.card W : ℝ) * (fhat W S r) ^ 2 ≤
        (Fintype.card T : ℝ) * ∑ r₁ ∈ fiberQ hTW q₁, (δ₁ (slice r₁)) ^ 2 := by
      linarith
    rw [le_div_iff₀ hK_pos]
    nlinarith

/-- Restricted boxing obtained by shrinking `B.W` to a submodule `T ≤ B.W`. -/
private noncomputable def restrictBoxing {n : ℕ} (B : Boxing n)
    (T : Submodule (ZMod 2) (𝔽₂ n)) (hTW : T ≤ B.W) : Boxing n where
  W := T
  m := B.m
  hm := B.hm
  labB r t := B.labB (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
    (shiftW hTW r.1 + ⟨t.val, hTW t.prop⟩)
  labC r t := B.labC (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
    (shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩)
  labD r t := B.labD (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
    (shiftW hTW r.1 + shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩)

private lemma Bset_restrictBoxing {n : ℕ} (B : Boxing n) (T : Submodule (ZMod 2) (𝔽₂ n))
    (hTW : T ≤ B.W) (r : Q T) (i : Fin B.m) :
    Bset (restrictBoxing B T hTW) r i =
    (univ.filter (fun t : T => B.labB (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.1 + ⟨t.val, hTW t.prop⟩) = i) : Finset T) :=
  rfl

private lemma Cset_restrictBoxing {n : ℕ} (B : Boxing n) (T : Submodule (ZMod 2) (𝔽₂ n))
    (hTW : T ≤ B.W) (r : Q T) (j : Fin B.m) :
    Cset (restrictBoxing B T hTW) r j =
    (univ.filter (fun t : T => B.labC (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩) = j) : Finset T) :=
  rfl

private lemma Dset_restrictBoxing {n : ℕ} (B : Boxing n) (T : Submodule (ZMod 2) (𝔽₂ n))
    (hTW : T ≤ B.W) (r : Q T) (k : Fin B.m) :
    Dset (restrictBoxing B T hTW) r k =
    (univ.filter (fun t : T => B.labD (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.1 + shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩) = k) : Finset T) :=
  rfl

/-- Scaling helper for `E₂` under subspace restriction. -/
private lemma innerTerm_fiber_ge {n : ℕ} {T W : Submodule (ZMod 2) (𝔽₂ n)} (hTW : T ≤ W)
    (q : Q W) (X Y : Finset W) (eW : W → W → Prop)
    (X' Y' : Q T → Finset T) (eT : Q T → T → T → Prop)
    (φ : W × W → Q T)
    (hmatch : ∀ r ∈ fiberQ hTW q.1 ×ˢ fiberQ hTW q.2,
      ((X ×ˢ Y).filter (fun p => φ p = r)).card = (X' r ×ˢ Y' r).card ∧
      (univ.filter (fun p : W × W => eW p.1 p.2) ∩
        (X ×ˢ Y).filter (fun p => φ p = r)).card =
      (univ.filter (fun p : T × T => eT r p.1 p.2) ∩ (X' r ×ˢ Y' r)).card)
    (hemp : ∀ r : Q T, r ∉ fiberQ hTW q.1 ×ˢ fiberQ hTW q.2 →
      (X ×ˢ Y).filter (fun p => φ p = r) = ∅) :
    ((fiberQ hTW q.1 ×ˢ fiberQ hTW q.2).card : ℝ) * innerTerm X Y eW ≤
    ∑ r ∈ fiberQ hTW q.1 ×ˢ fiberQ hTW q.2, innerTerm (X' r) (Y' r) (eT r) := by
  let fib2 : Finset (Q T) := fiberQ hTW q.1 ×ˢ fiberQ hTW q.2
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hT_pos : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hT2_pos : (0 : ℝ) < (Fintype.card T : ℝ) ^ 2 := pow_pos hT_pos 2
  have hcf : (fib2.card : ℝ) * (Fintype.card T : ℝ) ^ 2 = (Fintype.card W : ℝ) ^ 2 := by
    have h1 : ((fiberQ hTW q.1).card : ℝ) * (Fintype.card T : ℝ) = (Fintype.card W : ℝ) := by
      exact_mod_cast card_fiberQ_mul hTW q.1
    have h2 : ((fiberQ hTW q.2).card : ℝ) * (Fintype.card T : ℝ) = (Fintype.card W : ℝ) := by
      exact_mod_cast card_fiberQ_mul hTW q.2
    have hc : (fib2.card : ℝ) = ((fiberQ hTW q.1).card : ℝ) * ((fiberQ hTW q.2).card : ℝ) := by
      simp [fib2]
    nlinarith
  have hmono := partition_energy_mono (X ×ˢ Y) (univ.filter (fun p : W × W => eW p.1 p.2)) φ
  have hrhs : ∑ r : Q T, (((X ×ˢ Y).filter (fun p => φ p = r)).card : ℝ) *
      (setDens ((X ×ˢ Y).filter (fun p => φ p = r))
        (univ.filter (fun p : W × W => eW p.1 p.2))) ^ 2 =
      (Fintype.card T : ℝ) ^ 2 * ∑ r ∈ fib2, innerTerm (X' r) (Y' r) (eT r) := by
    rw [← Finset.sum_subset (Finset.subset_univ fib2)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [innerTerm_eq_setDens]
      rcases hmatch r hr with ⟨hc1, hc2⟩
      have hsd : setDens ((X ×ˢ Y).filter (fun p => φ p = r))
          (univ.filter (fun p : W × W => eW p.1 p.2)) =
          setDens (X' r ×ˢ Y' r) (univ.filter (fun p : T × T => eT r p.1 p.2)) := by
        unfold setDens; rw [hc1, hc2]
      rw [hc1, hsd]
      field_simp [hT_pos.ne']
    · intro r _ hr
      rw [hemp r hr]; simp
  rw [hrhs] at hmono
  rw [innerTerm_eq_setDens]
  have hdiv : (fib2.card : ℝ) *
      (((X ×ˢ Y).card : ℝ) * (setDens (X ×ˢ Y) (univ.filter (fun p : W × W => eW p.1 p.2))) ^ 2 /
        (Fintype.card W : ℝ) ^ 2) =
      (((X ×ˢ Y).card : ℝ) * (setDens (X ×ˢ Y) (univ.filter (fun p : W × W => eW p.1 p.2))) ^ 2) /
        (Fintype.card T : ℝ) ^ 2 := by
    field_simp [hW_pos.ne', hT_pos.ne']
    have hmul := congrArg (· * (((X ×ˢ Y).card : ℝ) *
      (setDens (X ×ˢ Y) (univ.filter (fun p : W × W => eW p.1 p.2))) ^ 2)) hcf
    linarith
  rw [hdiv, div_le_iff₀ hT2_pos]
  linarith

private lemma innerTerm_restrict_BC {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (T : Submodule (ZMod 2) (𝔽₂ n)) (hTW : T ≤ B.W) (q : Q B.W) (i j : Fin B.m) :
    ((fiberQ hTW q.1 ×ˢ fiberQ hTW q.2).card : ℝ) *
      innerTerm (Bset B q i) (Cset B q j) (eBC A B.W q) ≤
    ∑ r ∈ fiberQ hTW q.1 ×ˢ fiberQ hTW q.2,
      innerTerm (Bset (restrictBoxing B T hTW) r i) (Cset (restrictBoxing B T hTW) r j)
        (eBC A T r) := by
  simp_rw [Bset_restrictBoxing, Cset_restrictBoxing]
  let φ : B.W × B.W → Q T := fun p =>
    (Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val),
     Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.2.val))
  let XB : Q T → Finset T := fun r =>
    univ.filter (fun t : T => B.labB (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.1 + ⟨t.val, hTW t.prop⟩) = i)
  let YC : Q T → Finset T := fun r =>
    univ.filter (fun t : T => B.labC (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩) = j)
  refine innerTerm_fiber_ge hTW q (Bset B q i) (Cset B q j) (eBC A B.W q)
    XB YC (fun r => eBC A T r) φ ?_ ?_
  · intro r hr
    simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and] at hr
    rcases hr with ⟨hr1, hr2⟩
    have hbij_gen : ∀ (P : B.W × B.W → Prop) (P' : T × T → Prop),
        (∀ (t₁ t₂ : T), P (shiftW hTW r.1 + ⟨t₁.val, hTW t₁.prop⟩,
          shiftW hTW r.2 + ⟨t₂.val, hTW t₂.prop⟩) ↔ P' (t₁, t₂)) →
        (((Bset B q i ×ˢ Cset B q j).filter (fun p => φ p = r)).filter P).card =
        ((XB r ×ˢ YC r).filter P').card := by
      intro P P' hP
      refine Finset.card_bij
        (fun p hp =>
          (⟨rep B.W q.1 + p.1.val + rep T r.1, by
            have hφ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have h1 : Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val) = r.1 :=
              congrArg Prod.fst hφ
            rw [← h1]; exact add_rep_mem T _⟩,
           ⟨rep B.W q.2 + p.2.val + rep T r.2, by
            have hφ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have h2 : Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.2.val) = r.2 :=
              congrArg Prod.snd hφ
            rw [← h2]; exact add_rep_mem T _⟩)) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
        rcases hp with ⟨⟨⟨hi, hj⟩, hφ⟩, hPp⟩
        have hp1 : shiftW hTW r.1 + ⟨rep B.W q.1 + p.1.val + rep T r.1,
            hTW (by rw [← congrArg Prod.fst hφ]; exact add_rep_mem T _)⟩ = p.1 := by
          apply Subtype.ext; simp only [Submodule.coe_add, shiftW, hr1]
          calc rep T r.1 + rep B.W q.1 + (rep B.W q.1 + p.1.val + rep T r.1)
              = (rep T r.1 + rep T r.1) + (rep B.W q.1 + rep B.W q.1) + p.1.val := by abel
            _ = p.1.val := by simp only [f2_add_self, zero_add]
        have hp2 : shiftW hTW r.2 + ⟨rep B.W q.2 + p.2.val + rep T r.2,
            hTW (by rw [← congrArg Prod.snd hφ]; exact add_rep_mem T _)⟩ = p.2 := by
          apply Subtype.ext; simp only [Submodule.coe_add, shiftW, hr2]
          calc rep T r.2 + rep B.W q.2 + (rep B.W q.2 + p.2.val + rep T r.2)
              = (rep T r.2 + rep T r.2) + (rep B.W q.2 + rep B.W q.2) + p.2.val := by abel
            _ = p.2.val := by simp only [f2_add_self, zero_add]
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩
        · rw [hr1, hr2, hp1]; exact (Finset.mem_filter.mp hi).2
        · rw [hr1, hr2, hp2]; exact (Finset.mem_filter.mp hj).2
        · rw [← hP, hp1, hp2]; exact hPp
      · intro p₁ _ p₂ _ h
        have h1 := congrArg (fun x => x.1.val) h
        have h2 := congrArg (fun x => x.2.val) h
        exact Prod.ext (Subtype.ext (add_left_cancel (add_right_cancel h1)))
          (Subtype.ext (add_left_cancel (add_right_cancel h2)))
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_product] at ht
        rcases ht with ⟨⟨hi, hj⟩, hPt⟩
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        refine ⟨(shiftW hTW r.1 + ⟨t.1.val, hTW t.1.prop⟩,
          shiftW hTW r.2 + ⟨t.2.val, hTW t.2.prop⟩), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩,
                    Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩, (hP t.1 t.2).mpr hPt⟩
          · rw [hr1, hr2] at hi'; exact hi'
          · rw [hr1, hr2] at hj'; exact hj'
          · ext
            · dsimp only [φ]; simp only [Submodule.coe_add, shiftW, hr1]
              have hs : rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t.1.val) = rep T r.1 + t.1.val := by
                calc rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t.1.val)
                    = (rep B.W q.1 + rep B.W q.1) + rep T r.1 + t.1.val := by abel
                  _ = rep T r.1 + t.1.val := by simp only [f2_add_self, zero_add]
              rw [hs]; change Submodule.Quotient.mk (p := T) (rep T r.1) +
                Submodule.Quotient.mk (p := T) t.1.val = r.1
              rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr t.1.prop, add_zero]
            · dsimp only [φ]; simp only [Submodule.coe_add, shiftW, hr2]
              have hs : rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t.2.val) = rep T r.2 + t.2.val := by
                calc rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t.2.val)
                    = (rep B.W q.2 + rep B.W q.2) + rep T r.2 + t.2.val := by abel
                  _ = rep T r.2 + t.2.val := by simp only [f2_add_self, zero_add]
              rw [hs]; change Submodule.Quotient.mk (p := T) (rep T r.2) +
                Submodule.Quotient.mk (p := T) t.2.val = r.2
              rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr t.2.prop, add_zero]
        · apply Prod.ext <;> apply Subtype.ext <;> simp only [Submodule.coe_add, shiftW, hr1, hr2]
          · calc rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t.1.val) + rep T r.1
                = (rep B.W q.1 + rep B.W q.1) + (rep T r.1 + rep T r.1) + t.1.val := by abel
              _ = t.1.val := by simp only [f2_add_self, zero_add]
          · calc rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t.2.val) + rep T r.2
                = (rep B.W q.2 + rep B.W q.2) + (rep T r.2 + rep T r.2) + t.2.val := by abel
              _ = t.2.val := by simp only [f2_add_self, zero_add]
    constructor
    · simpa [Finset.filter_true] using hbij_gen (fun _ => True) (fun _ => True) (fun _ _ => Iff.rfl)
    · have heq1 : univ.filter (fun p : B.W × B.W => eBC A B.W q p.1 p.2) ∩
          (Bset B q i ×ˢ Cset B q j).filter (fun p => φ p = r) =
          ((Bset B q i ×ˢ Cset B q j).filter (fun p => φ p = r)).filter (fun p => eBC A B.W q p.1 p.2) := by
        ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      have heq2 : univ.filter (fun p : T × T => eBC A T r p.1 p.2) ∩ (XB r ×ˢ YC r) =
          (XB r ×ˢ YC r).filter (fun p => eBC A T r p.1 p.2) := by
        ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      rw [heq1, heq2]
      refine hbij_gen (fun p => eBC A B.W q p.1 p.2) (fun p => eBC A T r p.1 p.2) fun t₁ t₂ => ?_
      simp only [eBC, A_box, mem_filter, mem_univ, true_and, Submodule.coe_add, shiftW, hr1, hr2]
      have h1 : rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t₁.val) = rep T r.1 + t₁.val := by
        calc rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t₁.val)
            = (rep B.W q.1 + rep B.W q.1) + rep T r.1 + t₁.val := by abel
          _ = rep T r.1 + t₁.val := by simp only [f2_add_self, zero_add]
      have h2 : rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t₂.val) = rep T r.2 + t₂.val := by
        calc rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t₂.val)
            = (rep B.W q.2 + rep B.W q.2) + rep T r.2 + t₂.val := by abel
          _ = rep T r.2 + t₂.val := by simp only [f2_add_self, zero_add]
      rw [h1, h2]
  · intro r hr
    ext p
    simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro _ hφ
    apply hr
    rw [← hφ]
    simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and, φ]
    constructor
    · rw [factor_mk' hTW]
      change Submodule.Quotient.mk (p := B.W) (rep B.W q.1) +
        Submodule.Quotient.mk (p := B.W) p.1.val = q.1
      rw [mk_rep, (Submodule.Quotient.mk_eq_zero B.W).mpr p.1.prop, add_zero]
    · rw [factor_mk' hTW]
      change Submodule.Quotient.mk (p := B.W) (rep B.W q.2) +
        Submodule.Quotient.mk (p := B.W) p.2.val = q.2
      rw [mk_rep, (Submodule.Quotient.mk_eq_zero B.W).mpr p.2.prop, add_zero]

private lemma innerTerm_restrict_BD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (T : Submodule (ZMod 2) (𝔽₂ n)) (hTW : T ≤ B.W) (q : Q B.W) (i k : Fin B.m) :
    ((fiberQ hTW q.1 ×ˢ fiberQ hTW q.2).card : ℝ) *
      innerTerm (Bset B q i) (Dset B q k) (eBD A B.W q) ≤
    ∑ r ∈ fiberQ hTW q.1 ×ˢ fiberQ hTW q.2,
      innerTerm (Bset (restrictBoxing B T hTW) r i) (Dset (restrictBoxing B T hTW) r k)
        (eBD A T r) := by
  simp_rw [Bset_restrictBoxing, Dset_restrictBoxing]
  let φ : B.W × B.W → Q T := fun p =>
    (Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val),
     Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val + p.2.val))
  let XB : Q T → Finset T := fun r =>
    univ.filter (fun t : T => B.labB (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.1 + ⟨t.val, hTW t.prop⟩) = i)
  let ZD : Q T → Finset T := fun r =>
    univ.filter (fun t : T => B.labD (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.1 + shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩) = k)
  refine innerTerm_fiber_ge hTW q (Bset B q i) (Dset B q k) (eBD A B.W q)
    XB ZD (fun r => eBD A T r) φ ?_ ?_
  · intro r hr
    simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and] at hr
    rcases hr with ⟨hr1, hr2⟩
    have hbij_gen : ∀ (P : B.W × B.W → Prop) (P' : T × T → Prop),
        (∀ (t₁ t₃ : T), P (shiftW hTW r.1 + ⟨t₁.val, hTW t₁.prop⟩,
          shiftW hTW r.1 + shiftW hTW r.2 + ⟨t₃.val, hTW t₃.prop⟩) ↔ P' (t₁, t₃)) →
        (((Bset B q i ×ˢ Dset B q k).filter (fun p => φ p = r)).filter P).card =
        ((XB r ×ˢ ZD r).filter P').card := by
      intro P P' hP
      refine Finset.card_bij
        (fun p hp =>
          (⟨rep B.W q.1 + p.1.val + rep T r.1, by
            have hφ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have h1 : Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val) = r.1 :=
              congrArg Prod.fst hφ
            rw [← h1]; exact add_rep_mem T _⟩,
           ⟨rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2, by
            have hφ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have h1 : Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val) = r.1 :=
              congrArg Prod.fst hφ
            have h2 : Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val + p.2.val) = r.2 :=
              congrArg Prod.snd hφ
            have hm1 : rep B.W q.1 + p.1.val + rep T r.1 ∈ T := by rw [← h1]; exact add_rep_mem T _
            have hm2 : rep B.W q.2 + p.1.val + p.2.val + rep T r.2 ∈ T := by rw [← h2]; exact add_rep_mem T _
            have hsum : (rep B.W q.1 + p.1.val + rep T r.1) + (rep B.W q.2 + p.1.val + p.2.val + rep T r.2) =
                rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by
              calc (rep B.W q.1 + p.1.val + rep T r.1) + (rep B.W q.2 + p.1.val + p.2.val + rep T r.2)
                  = (p.1.val + p.1.val) + rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by abel
                _ = rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by simp only [f2_add_self, zero_add]
            rw [← hsum]; exact T.add_mem hm1 hm2⟩)) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
        rcases hp with ⟨⟨⟨hi, hk⟩, hφ⟩, hPp⟩
        have hp1 : shiftW hTW r.1 + ⟨rep B.W q.1 + p.1.val + rep T r.1,
            hTW (by rw [← congrArg Prod.fst hφ]; exact add_rep_mem T _)⟩ = p.1 := by
          apply Subtype.ext; simp only [Submodule.coe_add, shiftW, hr1]
          calc rep T r.1 + rep B.W q.1 + (rep B.W q.1 + p.1.val + rep T r.1)
              = (rep T r.1 + rep T r.1) + (rep B.W q.1 + rep B.W q.1) + p.1.val := by abel
            _ = p.1.val := by simp only [f2_add_self, zero_add]
        have hp2 : shiftW hTW r.1 + shiftW hTW r.2 +
            ⟨rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2, by
              have h1 : Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val) = r.1 := congrArg Prod.fst hφ
              have h2 : Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val + p.2.val) = r.2 := congrArg Prod.snd hφ
              have hm1 : rep B.W q.1 + p.1.val + rep T r.1 ∈ T := by rw [← h1]; exact add_rep_mem T _
              have hm2 : rep B.W q.2 + p.1.val + p.2.val + rep T r.2 ∈ T := by rw [← h2]; exact add_rep_mem T _
              have hsum : (rep B.W q.1 + p.1.val + rep T r.1) + (rep B.W q.2 + p.1.val + p.2.val + rep T r.2) =
                  rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by
                calc (rep B.W q.1 + p.1.val + rep T r.1) + (rep B.W q.2 + p.1.val + p.2.val + rep T r.2)
                    = (p.1.val + p.1.val) + rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by abel
                  _ = rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by simp only [f2_add_self, zero_add]
              exact hTW (by rw [← hsum]; exact T.add_mem hm1 hm2)⟩ = p.2 := by
          apply Subtype.ext; simp only [Submodule.coe_add, shiftW, hr1, hr2]
          calc rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) +
                (rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2)
              = (rep T r.1 + rep T r.1) + (rep T r.2 + rep T r.2) +
                (rep B.W q.1 + rep B.W q.1) + (rep B.W q.2 + rep B.W q.2) + p.2.val := by abel
            _ = p.2.val := by simp only [f2_add_self, zero_add]
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩
        · rw [hr1, hr2, hp1]; exact (Finset.mem_filter.mp hi).2
        · rw [hr1, hr2, hp2]; exact (Finset.mem_filter.mp hk).2
        · rw [← hP, hp1, hp2]; exact hPp
      · intro p₁ _ p₂ _ h
        have h1 := congrArg (fun x => x.1.val) h
        have h2 := congrArg (fun x => x.2.val) h
        exact Prod.ext (Subtype.ext (add_left_cancel (add_right_cancel h1)))
          (Subtype.ext (add_left_cancel (add_right_cancel (add_right_cancel h2))))
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_product] at ht
        rcases ht with ⟨⟨hi, hk⟩, hPt⟩
        have hi' := (Finset.mem_filter.mp hi).2
        have hk' := (Finset.mem_filter.mp hk).2
        refine ⟨(shiftW hTW r.1 + ⟨t.1.val, hTW t.1.prop⟩,
          shiftW hTW r.1 + shiftW hTW r.2 + ⟨t.2.val, hTW t.2.prop⟩), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩,
                    Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩, (hP t.1 t.2).mpr hPt⟩
          · rw [hr1, hr2] at hi'; exact hi'
          · rw [hr1, hr2] at hk'; exact hk'
          · ext
            · dsimp only [φ]; simp only [Submodule.coe_add, shiftW, hr1]
              have hs : rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t.1.val) = rep T r.1 + t.1.val := by
                calc rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t.1.val)
                    = (rep B.W q.1 + rep B.W q.1) + rep T r.1 + t.1.val := by abel
                  _ = rep T r.1 + t.1.val := by simp only [f2_add_self, zero_add]
              rw [hs]; change Submodule.Quotient.mk (p := T) (rep T r.1) +
                Submodule.Quotient.mk (p := T) t.1.val = r.1
              rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr t.1.prop, add_zero]
            · dsimp only [φ]; simp only [Submodule.coe_add, shiftW, hr1, hr2]
              have hs : rep B.W q.2 + (rep T r.1 + rep B.W q.1 + t.1.val) +
                  (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t.2.val) =
                  rep T r.2 + (t.1.val + t.2.val) := by
                calc rep B.W q.2 + (rep T r.1 + rep B.W q.1 + t.1.val) +
                      (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t.2.val)
                    = (rep B.W q.2 + rep B.W q.2) + (rep B.W q.1 + rep B.W q.1) +
                      (rep T r.1 + rep T r.1) + rep T r.2 + (t.1.val + t.2.val) := by abel
                  _ = rep T r.2 + (t.1.val + t.2.val) := by simp only [f2_add_self, zero_add]
              rw [hs]; change Submodule.Quotient.mk (p := T) (rep T r.2) +
                Submodule.Quotient.mk (p := T) (t.1.val + t.2.val) = r.2
              rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr (T.add_mem t.1.prop t.2.prop), add_zero]
        · apply Prod.ext <;> apply Subtype.ext <;> simp only [Submodule.coe_add, shiftW, hr1, hr2]
          · calc rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t.1.val) + rep T r.1
                = (rep B.W q.1 + rep B.W q.1) + (rep T r.1 + rep T r.1) + t.1.val := by abel
              _ = t.1.val := by simp only [f2_add_self, zero_add]
          · calc rep B.W q.1 + rep B.W q.2 +
                  (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t.2.val) + rep T r.1 + rep T r.2
                = (rep B.W q.1 + rep B.W q.1) + (rep B.W q.2 + rep B.W q.2) +
                  (rep T r.1 + rep T r.1) + (rep T r.2 + rep T r.2) + t.2.val := by abel
              _ = t.2.val := by simp only [f2_add_self, zero_add]
    constructor
    · simpa [Finset.filter_true] using hbij_gen (fun _ => True) (fun _ => True) (fun _ _ => Iff.rfl)
    · have heq1 : univ.filter (fun p : B.W × B.W => eBD A B.W q p.1 p.2) ∩
          (Bset B q i ×ˢ Dset B q k).filter (fun p => φ p = r) =
          ((Bset B q i ×ˢ Dset B q k).filter (fun p => φ p = r)).filter (fun p => eBD A B.W q p.1 p.2) := by
        ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      have heq2 : univ.filter (fun p : T × T => eBD A T r p.1 p.2) ∩ (XB r ×ˢ ZD r) =
          (XB r ×ˢ ZD r).filter (fun p => eBD A T r p.1 p.2) := by
        ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      rw [heq1, heq2]
      refine hbij_gen (fun p => eBD A B.W q p.1 p.2) (fun p => eBD A T r p.1 p.2) fun t₁ t₃ => ?_
      simp only [eBD, A_box, mem_filter, mem_univ, true_and, Submodule.coe_add, shiftW, hr1, hr2]
      have h1 : rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t₁.val) = rep T r.1 + t₁.val := by
        calc rep B.W q.1 + (rep T r.1 + rep B.W q.1 + t₁.val)
            = (rep B.W q.1 + rep B.W q.1) + rep T r.1 + t₁.val := by abel
          _ = rep T r.1 + t₁.val := by simp only [f2_add_self, zero_add]
      have h2 : rep B.W q.2 + (rep T r.1 + rep B.W q.1 + t₁.val +
          (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t₃.val)) =
          rep T r.2 + (t₁.val + t₃.val) := by
        calc rep B.W q.2 + (rep T r.1 + rep B.W q.1 + t₁.val +
              (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t₃.val))
            = (rep B.W q.2 + rep B.W q.2) + (rep B.W q.1 + rep B.W q.1) +
              (rep T r.1 + rep T r.1) + rep T r.2 + (t₁.val + t₃.val) := by abel
          _ = rep T r.2 + (t₁.val + t₃.val) := by simp only [f2_add_self, zero_add]
      rw [h1, h2]
  · intro r hr
    ext p
    simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro _ hφ
    apply hr
    rw [← hφ]
    simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and, φ]
    constructor
    · rw [factor_mk' hTW]
      change Submodule.Quotient.mk (p := B.W) (rep B.W q.1) +
        Submodule.Quotient.mk (p := B.W) p.1.val = q.1
      rw [mk_rep, (Submodule.Quotient.mk_eq_zero B.W).mpr p.1.prop, add_zero]
    · rw [factor_mk' hTW]
      change (Submodule.Quotient.mk (p := B.W) (rep B.W q.2) +
        Submodule.Quotient.mk (p := B.W) p.1.val) +
        Submodule.Quotient.mk (p := B.W) p.2.val = q.2
      rw [mk_rep, (Submodule.Quotient.mk_eq_zero B.W).mpr p.1.prop,
        (Submodule.Quotient.mk_eq_zero B.W).mpr p.2.prop, add_zero, add_zero]

private lemma innerTerm_restrict_CD {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (T : Submodule (ZMod 2) (𝔽₂ n)) (hTW : T ≤ B.W) (q : Q B.W) (j k : Fin B.m) :
    ((fiberQ hTW q.1 ×ˢ fiberQ hTW q.2).card : ℝ) *
      innerTerm (Cset B q j) (Dset B q k) (eCD A B.W q) ≤
    ∑ r ∈ fiberQ hTW q.1 ×ˢ fiberQ hTW q.2,
      innerTerm (Cset (restrictBoxing B T hTW) r j) (Dset (restrictBoxing B T hTW) r k)
        (eCD A T r) := by
  simp_rw [Cset_restrictBoxing, Dset_restrictBoxing]
  let φ : B.W × B.W → Q T := fun p =>
    (Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val + p.2.val),
     Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val))
  let YC : Q T → Finset T := fun r =>
    univ.filter (fun t : T => B.labC (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩) = j)
  let ZD : Q T → Finset T := fun r =>
    univ.filter (fun t : T => B.labD (Submodule.factor hTW r.1, Submodule.factor hTW r.2)
      (shiftW hTW r.1 + shiftW hTW r.2 + ⟨t.val, hTW t.prop⟩) = k)
  refine innerTerm_fiber_ge hTW q (Cset B q j) (Dset B q k) (eCD A B.W q)
    YC ZD (fun r => eCD A T r) φ ?_ ?_
  · intro r hr
    simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and] at hr
    rcases hr with ⟨hr1, hr2⟩
    have hbij_gen : ∀ (P : B.W × B.W → Prop) (P' : T × T → Prop),
        (∀ (t₂ t₃ : T), P (shiftW hTW r.2 + ⟨t₂.val, hTW t₂.prop⟩,
          shiftW hTW r.1 + shiftW hTW r.2 + ⟨t₃.val, hTW t₃.prop⟩) ↔ P' (t₂, t₃)) →
        (((Cset B q j ×ˢ Dset B q k).filter (fun p => φ p = r)).filter P).card =
        ((YC r ×ˢ ZD r).filter P').card := by
      intro P P' hP
      refine Finset.card_bij
        (fun p hp =>
          (⟨rep B.W q.2 + p.1.val + rep T r.2, by
            have hφ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have h2 : Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val) = r.2 :=
              congrArg Prod.snd hφ
            rw [← h2]; exact add_rep_mem T _⟩,
           ⟨rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2, by
            have hφ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have h1 : Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val + p.2.val) = r.1 :=
              congrArg Prod.fst hφ
            have h2 : Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val) = r.2 :=
              congrArg Prod.snd hφ
            have hm1 : rep B.W q.1 + p.1.val + p.2.val + rep T r.1 ∈ T := by rw [← h1]; exact add_rep_mem T _
            have hm2 : rep B.W q.2 + p.1.val + rep T r.2 ∈ T := by rw [← h2]; exact add_rep_mem T _
            have hsum : (rep B.W q.1 + p.1.val + p.2.val + rep T r.1) + (rep B.W q.2 + p.1.val + rep T r.2) =
                rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by
              calc (rep B.W q.1 + p.1.val + p.2.val + rep T r.1) + (rep B.W q.2 + p.1.val + rep T r.2)
                  = (p.1.val + p.1.val) + rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by abel
                _ = rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by simp only [f2_add_self, zero_add]
            rw [← hsum]; exact T.add_mem hm1 hm2⟩)) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
        rcases hp with ⟨⟨⟨hj, hk⟩, hφ⟩, hPp⟩
        have hp1 : shiftW hTW r.2 + ⟨rep B.W q.2 + p.1.val + rep T r.2,
            hTW (by rw [← congrArg Prod.snd hφ]; exact add_rep_mem T _)⟩ = p.1 := by
          apply Subtype.ext; simp only [Submodule.coe_add, shiftW, hr2]
          calc rep T r.2 + rep B.W q.2 + (rep B.W q.2 + p.1.val + rep T r.2)
              = (rep T r.2 + rep T r.2) + (rep B.W q.2 + rep B.W q.2) + p.1.val := by abel
            _ = p.1.val := by simp only [f2_add_self, zero_add]
        have hp2 : shiftW hTW r.1 + shiftW hTW r.2 +
            ⟨rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2, by
              have h1 : Submodule.Quotient.mk (p := T) (rep B.W q.1 + p.1.val + p.2.val) = r.1 := congrArg Prod.fst hφ
              have h2 : Submodule.Quotient.mk (p := T) (rep B.W q.2 + p.1.val) = r.2 := congrArg Prod.snd hφ
              have hm1 : rep B.W q.1 + p.1.val + p.2.val + rep T r.1 ∈ T := by rw [← h1]; exact add_rep_mem T _
              have hm2 : rep B.W q.2 + p.1.val + rep T r.2 ∈ T := by rw [← h2]; exact add_rep_mem T _
              have hsum : (rep B.W q.1 + p.1.val + p.2.val + rep T r.1) + (rep B.W q.2 + p.1.val + rep T r.2) =
                  rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by
                calc (rep B.W q.1 + p.1.val + p.2.val + rep T r.1) + (rep B.W q.2 + p.1.val + rep T r.2)
                    = (p.1.val + p.1.val) + rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by abel
                  _ = rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2 := by simp only [f2_add_self, zero_add]
              exact hTW (by rw [← hsum]; exact T.add_mem hm1 hm2)⟩ = p.2 := by
          apply Subtype.ext; simp only [Submodule.coe_add, shiftW, hr1, hr2]
          calc rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) +
                (rep B.W q.1 + rep B.W q.2 + p.2.val + rep T r.1 + rep T r.2)
              = (rep T r.1 + rep T r.1) + (rep T r.2 + rep T r.2) +
                (rep B.W q.1 + rep B.W q.1) + (rep B.W q.2 + rep B.W q.2) + p.2.val := by abel
            _ = p.2.val := by simp only [f2_add_self, zero_add]
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩
        · rw [hr1, hr2, hp1]; exact (Finset.mem_filter.mp hj).2
        · rw [hr1, hr2, hp2]; exact (Finset.mem_filter.mp hk).2
        · rw [← hP, hp1, hp2]; exact hPp
      · intro p₁ _ p₂ _ h
        have h1 := congrArg (fun x => x.1.val) h
        have h2 := congrArg (fun x => x.2.val) h
        exact Prod.ext (Subtype.ext (add_left_cancel (add_right_cancel h1)))
          (Subtype.ext (add_left_cancel (add_right_cancel (add_right_cancel h2))))
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_product] at ht
        rcases ht with ⟨⟨hj, hk⟩, hPt⟩
        have hj' := (Finset.mem_filter.mp hj).2
        have hk' := (Finset.mem_filter.mp hk).2
        refine ⟨(shiftW hTW r.2 + ⟨t.1.val, hTW t.1.prop⟩,
          shiftW hTW r.1 + shiftW hTW r.2 + ⟨t.2.val, hTW t.2.prop⟩), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩,
                    Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, ?_⟩, (hP t.1 t.2).mpr hPt⟩
          · rw [hr1, hr2] at hj'; exact hj'
          · rw [hr1, hr2] at hk'; exact hk'
          · ext
            · dsimp only [φ]; simp only [Submodule.coe_add, shiftW, hr1, hr2]
              have hs : rep B.W q.1 + (rep T r.2 + rep B.W q.2 + t.1.val) +
                  (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t.2.val) =
                  rep T r.1 + (t.1.val + t.2.val) := by
                calc rep B.W q.1 + (rep T r.2 + rep B.W q.2 + t.1.val) +
                      (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t.2.val)
                    = (rep B.W q.1 + rep B.W q.1) + (rep B.W q.2 + rep B.W q.2) +
                      (rep T r.2 + rep T r.2) + rep T r.1 + (t.1.val + t.2.val) := by abel
                  _ = rep T r.1 + (t.1.val + t.2.val) := by simp only [f2_add_self, zero_add]
              rw [hs]; change Submodule.Quotient.mk (p := T) (rep T r.1) +
                Submodule.Quotient.mk (p := T) (t.1.val + t.2.val) = r.1
              rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr (T.add_mem t.1.prop t.2.prop), add_zero]
            · dsimp only [φ]; simp only [Submodule.coe_add, shiftW, hr2]
              have hs : rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t.1.val) = rep T r.2 + t.1.val := by
                calc rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t.1.val)
                    = (rep B.W q.2 + rep B.W q.2) + rep T r.2 + t.1.val := by abel
                  _ = rep T r.2 + t.1.val := by simp only [f2_add_self, zero_add]
              rw [hs]; change Submodule.Quotient.mk (p := T) (rep T r.2) +
                Submodule.Quotient.mk (p := T) t.1.val = r.2
              rw [mk_rep, (Submodule.Quotient.mk_eq_zero T).mpr t.1.prop, add_zero]
        · apply Prod.ext <;> apply Subtype.ext <;> simp only [Submodule.coe_add, shiftW, hr1, hr2]
          · calc rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t.1.val) + rep T r.2
                = (rep B.W q.2 + rep B.W q.2) + (rep T r.2 + rep T r.2) + t.1.val := by abel
              _ = t.1.val := by simp only [f2_add_self, zero_add]
          · calc rep B.W q.1 + rep B.W q.2 +
                  (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t.2.val) + rep T r.1 + rep T r.2
                = (rep B.W q.1 + rep B.W q.1) + (rep B.W q.2 + rep B.W q.2) +
                  (rep T r.1 + rep T r.1) + (rep T r.2 + rep T r.2) + t.2.val := by abel
              _ = t.2.val := by simp only [f2_add_self, zero_add]
    constructor
    · simpa [Finset.filter_true] using hbij_gen (fun _ => True) (fun _ => True) (fun _ _ => Iff.rfl)
    · have heq1 : univ.filter (fun p : B.W × B.W => eCD A B.W q p.1 p.2) ∩
          (Cset B q j ×ˢ Dset B q k).filter (fun p => φ p = r) =
          ((Cset B q j ×ˢ Dset B q k).filter (fun p => φ p = r)).filter (fun p => eCD A B.W q p.1 p.2) := by
        ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      have heq2 : univ.filter (fun p : T × T => eCD A T r p.1 p.2) ∩ (YC r ×ˢ ZD r) =
          (YC r ×ˢ ZD r).filter (fun p => eCD A T r p.1 p.2) := by
        ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      rw [heq1, heq2]
      refine hbij_gen (fun p => eCD A B.W q p.1 p.2) (fun p => eCD A T r p.1 p.2) fun t₂ t₃ => ?_
      simp only [eCD, A_box, mem_filter, mem_univ, true_and, Submodule.coe_add, shiftW, hr1, hr2]
      have h1 : rep B.W q.1 + (rep T r.2 + rep B.W q.2 + t₂.val +
          (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t₃.val)) =
          rep T r.1 + (t₂.val + t₃.val) := by
        calc rep B.W q.1 + (rep T r.2 + rep B.W q.2 + t₂.val +
              (rep T r.1 + rep B.W q.1 + (rep T r.2 + rep B.W q.2) + t₃.val))
            = (rep B.W q.1 + rep B.W q.1) + (rep B.W q.2 + rep B.W q.2) +
              (rep T r.2 + rep T r.2) + rep T r.1 + (t₂.val + t₃.val) := by abel
          _ = rep T r.1 + (t₂.val + t₃.val) := by simp only [f2_add_self, zero_add]
      have h2 : rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t₂.val) = rep T r.2 + t₂.val := by
        calc rep B.W q.2 + (rep T r.2 + rep B.W q.2 + t₂.val)
            = (rep B.W q.2 + rep B.W q.2) + rep T r.2 + t₂.val := by abel
          _ = rep T r.2 + t₂.val := by simp only [f2_add_self, zero_add]
      rw [h1, h2]
  · intro r hr
    ext p
    simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro _ hφ
    apply hr
    rw [← hφ]
    simp only [mem_product, fiberQ, mem_filter, mem_univ, true_and, φ]
    constructor
    · rw [factor_mk' hTW]
      change (Submodule.Quotient.mk (p := B.W) (rep B.W q.1) +
        Submodule.Quotient.mk (p := B.W) p.1.val) +
        Submodule.Quotient.mk (p := B.W) p.2.val = q.1
      rw [mk_rep, (Submodule.Quotient.mk_eq_zero B.W).mpr p.1.prop,
        (Submodule.Quotient.mk_eq_zero B.W).mpr p.2.prop, add_zero, add_zero]
    · rw [factor_mk' hTW]
      change Submodule.Quotient.mk (p := B.W) (rep B.W q.2) +
        Submodule.Quotient.mk (p := B.W) p.1.val = q.2
      rw [mk_rep, (Submodule.Quotient.mk_eq_zero B.W).mpr p.1.prop, add_zero]

/-- `E₂` does not decrease under `restrictBoxing`. -/
private lemma E₂_restrictBoxing_ge {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n)
    (T : Submodule (ZMod 2) (𝔽₂ n)) (hTW : T ≤ B.W) :
    E₂ A B ≤ E₂ A (restrictBoxing B T hTW) := by
  have hT_pos : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hQW_pos : (0 : ℝ) < (Fintype.card (Q B.W) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hQT_pos : (0 : ℝ) < (Fintype.card (Q T) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let fib2 : Q B.W → Finset (Q T) := fun q => fiberQ hTW q.1 ×ˢ fiberQ hTW q.2
  have hcard_fib2 : ∀ q : Q B.W, ((fib2 q).card : ℝ) * (Fintype.card T : ℝ) ^ 2 =
      (Fintype.card B.W : ℝ) ^ 2 := by
    intro q
    have h1 : ((fiberQ hTW q.1).card : ℝ) * (Fintype.card T : ℝ) = (Fintype.card B.W : ℝ) := by
      exact_mod_cast card_fiberQ_mul hTW q.1
    have h2 : ((fiberQ hTW q.2).card : ℝ) * (Fintype.card T : ℝ) = (Fintype.card B.W : ℝ) := by
      exact_mod_cast card_fiberQ_mul hTW q.2
    have hc : ((fib2 q).card : ℝ) = ((fiberQ hTW q.1).card : ℝ) * ((fiberQ hTW q.2).card : ℝ) := by
      simp [fib2]
    nlinarith
  have hcard_QT : (Fintype.card (Q T) : ℝ) * (Fintype.card T : ℝ) ^ 2 =
      (Fintype.card (Q B.W) : ℝ) * (Fintype.card B.W : ℝ) ^ 2 := by
    have h1 : (Fintype.card (𝔽₂ n ⧸ T) : ℝ) * (Fintype.card T : ℝ) = (Fintype.card (𝔽₂ n) : ℝ) := by
      exact_mod_cast card_quot_mul_card_subspace T
    have h2 : (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ) * (Fintype.card B.W : ℝ) = (Fintype.card (𝔽₂ n) : ℝ) := by
      exact_mod_cast card_quot_mul_card_subspace B.W
    have hQT : (Fintype.card (Q T) : ℝ) = (Fintype.card (𝔽₂ n ⧸ T) : ℝ) ^ 2 := by simp [Q, sq]
    have hQW : (Fintype.card (Q B.W) : ℝ) = (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ) ^ 2 := by simp [Q, sq]
    nlinarith
  have hbox_ge : ∀ q : Q B.W,
      ((fib2 q).card : ℝ) * E₂_box A B q ≤ ∑ r ∈ fib2 q, E₂_box A (restrictBoxing B T hTW) r := by
    intro q
    unfold E₂_box
    rw [mul_div_assoc', ← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine sum_le_sum fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine sum_le_sum fun j _ => ?_
    simp only [Finset.sum_add_distrib]
    rw [mul_add, mul_add]
    exact add_le_add (add_le_add (innerTerm_restrict_BC A B T hTW q i j)
      (innerTerm_restrict_BD A B T hTW q i j))
      (innerTerm_restrict_CD A B T hTW q i j)
  have hsum_tot : ∑ q : Q B.W, ((fib2 q).card : ℝ) * E₂_box A B q ≤
      ∑ r : Q T, E₂_box A (restrictBoxing B T hTW) r := by
    calc ∑ q : Q B.W, ((fib2 q).card : ℝ) * E₂_box A B q
        ≤ ∑ q : Q B.W, ∑ r ∈ fib2 q, E₂_box A (restrictBoxing B T hTW) r :=
          sum_le_sum fun q _ => hbox_ge q
      _ = ∑ r : Q T, E₂_box A (restrictBoxing B T hTW) r := by
          have heq : ∀ q : Q B.W, fib2 q =
              univ.filter (fun r : Q T => (Submodule.factor hTW r.1, Submodule.factor hTW r.2) = q) := by
            intro q; ext r; simp [fib2, fiberQ, Prod.ext_iff]
          simp_rw [heq]
          exact Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ)
            (g := fun r : Q T => (Submodule.factor hTW r.1, Submodule.factor hTW r.2))
            (f := fun r : Q T => E₂_box A (restrictBoxing B T hTW) r) (fun _ _ => mem_univ _)
  have hfib_const : ∀ q : Q B.W, ((fib2 q).card : ℝ) =
      (Fintype.card (Q T) : ℝ) / (Fintype.card (Q B.W) : ℝ) := by
    intro q
    have h1 := hcard_fib2 q
    rw [eq_div_iff hQW_pos.ne']
    have hT2_ne : (Fintype.card T : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hT_pos.ne'
    apply mul_right_cancel₀ hT2_ne
    have hmul := congrArg (· * (Fintype.card (Q B.W) : ℝ)) h1
    linarith
  simp_rw [hfib_const, ← Finset.mul_sum] at hsum_tot
  unfold E₂
  change (∑ q : Q B.W, E₂_box A B q) / (Fintype.card (Q B.W) : ℝ) ≤
    (∑ r : Q T, E₂_box A (restrictBoxing B T hTW) r) / (Fintype.card (Q T) : ℝ)
  rw [div_le_div_iff₀ hQW_pos hQT_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hQW_pos] at hsum_tot
  linarith

/-- Codimension increases by at most 1 when intersecting with `ker (dotLM r)`. -/
private lemma codim_inf_ker_le {n : ℕ} (M : Submodule (ZMod 2) (𝔽₂ n)) (r : 𝔽₂ n) :
    codim (M ⊓ LinearMap.ker (dotLM r)) ≤ codim M + 1 := by
  let f : M →ₗ[ZMod 2] ZMod 2 := (dotLM r).comp M.subtype
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) (M ⊓ LinearMap.ker (dotLM r) : Submodule (ZMod 2) (𝔽₂ n)) := by
    let e : LinearMap.ker f ≃ₗ[ZMod 2] (M ⊓ LinearMap.ker (dotLM r) : Submodule (ZMod 2) (𝔽₂ n)) :=
      { toFun := fun x => ⟨x.val.val, ⟨x.val.prop, x.prop⟩⟩
        invFun := fun y => ⟨⟨y.val, y.prop.1⟩, y.prop.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrng : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    have hle := Submodule.finrank_le (LinearMap.range f)
    have hz : Module.finrank (ZMod 2) (ZMod 2) = 1 := Module.finrank_self (ZMod 2)
    omega
  have hc1 := codim_add_finrank M
  have hc2 := codim_add_finrank (M ⊓ LinearMap.ker (dotLM r))
  omega

/-- `E₁` increment for an abstract subspace `T ≤ B.W` killing the witnessing frequencies of `Bad₁`. -/
private lemma E₁_restrictBoxing_ge {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (B : Boxing n) (Bad₁ : Finset (Q B.W)) (rOf : Q B.W → 𝔽₂ n)
    (T : Submodule (ZMod 2) (𝔽₂ n)) (hTW : T ≤ B.W)
    (hTker : ∀ q ∈ Bad₁, T ≤ LinearMap.ker (dotLM (rOf q)))
    (hBad_gt : ε * (Fintype.card (Q B.W) : ℝ) < (Bad₁.card : ℝ))
    (hwit : ∀ q ∈ Bad₁, rOf q ∉ ann B.W ∧ ∃ i : Fin B.m,
      ε / (B.m : ℝ) ^ 3 < |fhat B.W (Bset B q i) (rOf q)| ∨
      ε / (B.m : ℝ) ^ 3 < |fhat B.W (Cset B q i) (rOf q)| ∨
      ε / (B.m : ℝ) ^ 3 < |fhat B.W (Dset B q i) (rOf q)|) :
    E₁ B + ε ^ 3 / (3 * (B.m : ℝ) ^ 6) ≤ E₁ (restrictBoxing B T hTW) := by
  let B' := restrictBoxing B T hTW
  have hW_pos : (0 : ℝ) < (Fintype.card B.W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hT_pos : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hQW_pos : (0 : ℝ) < (Fintype.card (Q B.W) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hQT_pos : (0 : ℝ) < (Fintype.card (Q T) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let fib2 : Q B.W → Finset (Q T) := fun q => fiberQ hTW q.1 ×ˢ fiberQ hTW q.2
  have hcard_fib : ∀ q₁ : 𝔽₂ n ⧸ B.W, ((fiberQ hTW q₁).card : ℝ) * (Fintype.card T : ℝ) =
      (Fintype.card B.W : ℝ) := fun q₁ => by exact_mod_cast card_fiberQ_mul hTW q₁
  have hK_pos : ∀ q₁ : 𝔽₂ n ⧸ B.W, (0 : ℝ) < ((fiberQ hTW q₁).card : ℝ) := fun q₁ => by
    have := hcard_fib q₁; nlinarith
  have hcard_QT : (Fintype.card (Q T) : ℝ) * (Fintype.card T : ℝ) ^ 2 =
      (Fintype.card (Q B.W) : ℝ) * (Fintype.card B.W : ℝ) ^ 2 := by
    have h1 : (Fintype.card (𝔽₂ n ⧸ T) : ℝ) * (Fintype.card T : ℝ) = (Fintype.card (𝔽₂ n) : ℝ) := by
      exact_mod_cast card_quot_mul_card_subspace T
    have h2 : (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ) * (Fintype.card B.W : ℝ) = (Fintype.card (𝔽₂ n) : ℝ) := by
      exact_mod_cast card_quot_mul_card_subspace B.W
    have hQT : (Fintype.card (Q T) : ℝ) = (Fintype.card (𝔽₂ n ⧸ T) : ℝ) ^ 2 := by simp [Q, sq]
    have hQW : (Fintype.card (Q B.W) : ℝ) = (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ) ^ 2 := by simp [Q, sq]
    nlinarith
  have hfib_const : ∀ q : Q B.W, ((fib2 q).card : ℝ) =
      (Fintype.card (Q T) : ℝ) / (Fintype.card (Q B.W) : ℝ) := by
    intro q
    have hc : ((fib2 q).card : ℝ) = ((fiberQ hTW q.1).card : ℝ) * ((fiberQ hTW q.2).card : ℝ) := by
      simp [fib2]
    rw [eq_div_iff hQW_pos.ne']
    have hT2_ne : (Fintype.card T : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hT_pos.ne'
    apply mul_right_cancel₀ hT2_ne
    have h1 := hcard_fib q.1
    have h2 := hcard_fib q.2
    have hsq : ((fib2 q).card : ℝ) * (Fintype.card T : ℝ) ^ 2 = (Fintype.card B.W : ℝ) ^ 2 := by
      rw [hc]; nlinarith
    have hmul := congrArg (· * (Fintype.card (Q B.W) : ℝ)) hsq
    linarith
  have hbox_E1 : ∀ q : Q B.W,
      ((fib2 q).card : ℝ) *
        (E₁_box B q + if q ∈ Bad₁ then ε ^ 2 / (3 * (B.m : ℝ) ^ 6) else 0) ≤
      ∑ r ∈ fib2 q, E₁_box B' r := by
    intro q
    set K1 : ℝ := ((fiberQ hTW q.1).card : ℝ)
    set K2 : ℝ := ((fiberQ hTW q.2).card : ℝ)
    have hK1 : 0 < K1 := hK_pos q.1
    have hK2 : 0 < K2 := hK_pos q.2
    have hfib_card : ((fib2 q).card : ℝ) = K1 * K2 := by simp [fib2, K1, K2]
    have hB_slice : ∀ i : Fin B.m,
        ∑ r ∈ fib2 q, (δ₁ (Bset (restrictBoxing B T hTW) r i)) ^ 2 =
        K2 * ∑ r₁ ∈ fiberQ hTW q.1,
          (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩ ∈ Bset B q i))) ^ 2 := by
      intro i
      rw [Finset.sum_product]
      have hinner : ∀ r₁ ∈ fiberQ hTW q.1, ∀ r₂ ∈ fiberQ hTW q.2,
          (δ₁ (Bset (restrictBoxing B T hTW) (r₁, r₂) i)) ^ 2 =
          (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩ ∈ Bset B q i))) ^ 2 := by
        intro r₁ hr₁ r₂ hr₂
        simp only [fiberQ, mem_filter, mem_univ, true_and] at hr₁ hr₂
        have hset : (Bset (restrictBoxing B T hTW) (r₁, r₂) i : Finset T) =
            univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩ ∈ Bset B q i) := by
          ext t
          change t ∈ (univ.filter (fun t : T =>
            B.labB (Submodule.factor hTW r₁, Submodule.factor hTW r₂)
              (shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩) = i) : Finset T) ↔ _
          simp only [Bset, mem_filter, mem_univ, true_and, zero_add, hr₁, hr₂]; exact Iff.rfl
        exact congrArg (fun S : Finset T => (δ₁ S) ^ 2) hset
      calc ∑ r₁ ∈ fiberQ hTW q.1, ∑ r₂ ∈ fiberQ hTW q.2, (δ₁ (Bset (restrictBoxing B T hTW) (r₁, r₂) i)) ^ 2
          = ∑ r₁ ∈ fiberQ hTW q.1, ∑ _r₂ ∈ fiberQ hTW q.2,
              (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩ ∈ Bset B q i))) ^ 2 :=
            Finset.sum_congr rfl fun r₁ hr₁ => Finset.sum_congr rfl fun r₂ hr₂ => hinner r₁ hr₁ r₂ hr₂
        _ = K2 * ∑ r₁ ∈ fiberQ hTW q.1,
              (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₁ + ⟨t.val, hTW t.prop⟩ ∈ Bset B q i))) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul, K2, Finset.mul_sum]
    have hC_slice : ∀ i : Fin B.m,
        ∑ r ∈ fib2 q, (δ₁ (Cset (restrictBoxing B T hTW) r i)) ^ 2 =
        K1 * ∑ r₂ ∈ fiberQ hTW q.2,
          (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Cset B q i))) ^ 2 := by
      intro i
      rw [Finset.sum_product, Finset.sum_comm]
      have hinner : ∀ r₁ ∈ fiberQ hTW q.1, ∀ r₂ ∈ fiberQ hTW q.2,
          (δ₁ (Cset (restrictBoxing B T hTW) (r₁, r₂) i)) ^ 2 =
          (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Cset B q i))) ^ 2 := by
        intro r₁ hr₁ r₂ hr₂
        simp only [fiberQ, mem_filter, mem_univ, true_and] at hr₁ hr₂
        have hset : (Cset (restrictBoxing B T hTW) (r₁, r₂) i : Finset T) =
            univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Cset B q i) := by
          ext t
          change t ∈ (univ.filter (fun t : T =>
            B.labC (Submodule.factor hTW r₁, Submodule.factor hTW r₂)
              (shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩) = i) : Finset T) ↔ _
          simp only [Cset, mem_filter, mem_univ, true_and, zero_add, hr₁, hr₂]; exact Iff.rfl
        exact congrArg (fun S : Finset T => (δ₁ S) ^ 2) hset
      calc ∑ r₂ ∈ fiberQ hTW q.2, ∑ r₁ ∈ fiberQ hTW q.1, (δ₁ (Cset (restrictBoxing B T hTW) (r₁, r₂) i)) ^ 2
          = ∑ r₂ ∈ fiberQ hTW q.2, ∑ _r₁ ∈ fiberQ hTW q.1,
              (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Cset B q i))) ^ 2 :=
            Finset.sum_congr rfl fun r₂ hr₂ => Finset.sum_congr rfl fun r₁ hr₁ => hinner r₁ hr₁ r₂ hr₂
        _ = K1 * ∑ r₂ ∈ fiberQ hTW q.2,
              (δ₁ (univ.filter (fun t : T => (0 : B.W) + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Cset B q i))) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul, K1, Finset.mul_sum]
    have hD_slice : ∀ i : Fin B.m,
        ∑ r ∈ fib2 q, (δ₁ (Dset (restrictBoxing B T hTW) r i)) ^ 2 =
        ∑ r₁ ∈ fiberQ hTW q.1, ∑ r₂ ∈ fiberQ hTW q.2,
          (δ₁ (univ.filter (fun t : T => shiftW hTW r₁ + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Dset B q i))) ^ 2 := by
      intro i
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun r₁ hr₁ => Finset.sum_congr rfl fun r₂ hr₂ => ?_
      simp only [fiberQ, mem_filter, mem_univ, true_and] at hr₁ hr₂
      have hset : (Dset (restrictBoxing B T hTW) (r₁, r₂) i : Finset T) =
          univ.filter (fun t : T => shiftW hTW r₁ + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Dset B q i) := by
        ext t
        change t ∈ (univ.filter (fun t : T =>
          B.labD (Submodule.factor hTW r₁, Submodule.factor hTW r₂)
            (shiftW hTW r₁ + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩) = i) : Finset T) ↔ _
        simp only [Dset, mem_filter, mem_univ, true_and, hr₁, hr₂]; exact Iff.rfl
      exact congrArg (fun S : Finset T => (δ₁ S) ^ 2) hset
    have hB_ge : ∀ i : Fin B.m, K1 * K2 * (δ₁ (Bset B q i)) ^ 2 ≤ ∑ r ∈ fib2 q, (δ₁ (Bset B' r i)) ^ 2 := by
      intro i
      rw [hB_slice i]
      have h := (coset_slice_energy_bound hTW q.1 0 (Bset B q i)).1
      rw [le_div_iff₀ hK1] at h
      nlinarith
    have hC_ge : ∀ i : Fin B.m, K1 * K2 * (δ₁ (Cset B q i)) ^ 2 ≤ ∑ r ∈ fib2 q, (δ₁ (Cset B' r i)) ^ 2 := by
      intro i
      rw [hC_slice i]
      have h := (coset_slice_energy_bound hTW q.2 0 (Cset B q i)).1
      rw [le_div_iff₀ hK2] at h
      nlinarith
    have hD_ge : ∀ i : Fin B.m, K1 * K2 * (δ₁ (Dset B q i)) ^ 2 ≤ ∑ r ∈ fib2 q, (δ₁ (Dset B' r i)) ^ 2 := by
      intro i
      rw [hD_slice i]
      calc K1 * K2 * (δ₁ (Dset B q i)) ^ 2
          = ∑ _r₁ ∈ fiberQ hTW q.1, (K2 * (δ₁ (Dset B q i)) ^ 2) := by
            simp [Finset.sum_const, nsmul_eq_mul, K1]; ring
        _ ≤ ∑ r₁ ∈ fiberQ hTW q.1, ∑ r₂ ∈ fiberQ hTW q.2,
              (δ₁ (univ.filter (fun t : T => shiftW hTW r₁ + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Dset B q i))) ^ 2 := by
            refine sum_le_sum fun r₁ _ => ?_
            have h := (coset_slice_energy_bound hTW q.2 (shiftW hTW r₁) (Dset B q i)).1
            rw [le_div_iff₀ hK2] at h
            linarith
    have hE1_sum : ∑ r ∈ fib2 q, E₁_box B' r =
        (∑ i : Fin B.m, ((∑ r ∈ fib2 q, (δ₁ (Bset B' r i)) ^ 2) +
          (∑ r ∈ fib2 q, (δ₁ (Cset B' r i)) ^ 2) +
          (∑ r ∈ fib2 q, (δ₁ (Dset B' r i)) ^ 2))) / 3 := by
      unfold E₁_box
      rw [← Finset.sum_div, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by simp only [Finset.sum_add_distrib]
    rw [hfib_card, hE1_sum]
    split_ifs with hq
    · rcases hwit q hq with ⟨hr_not_ann, i₀, hbig⟩
      have hT_dot : ∀ t : T, dot (rOf q) t.val = 0 := fun t => hTker q hq t.prop
      have hsq_lt : ∀ x : ℝ, ε / (B.m : ℝ) ^ 3 < |x| → ε ^ 2 / (B.m : ℝ) ^ 6 ≤ x ^ 2 := by
        intro x hx
        have h0 : 0 ≤ ε / (B.m : ℝ) ^ 3 := by positivity
        have hsq : (ε / (B.m : ℝ) ^ 3) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ h0 hx.le 2
        rw [sq_abs] at hsq
        have heq : (ε / (B.m : ℝ) ^ 3) ^ 2 = ε ^ 2 / (B.m : ℝ) ^ 6 := by ring
        linarith
      have hbonus : K1 * K2 * ((δ₁ (Bset B q i₀)) ^ 2 + (δ₁ (Cset B q i₀)) ^ 2 +
          (δ₁ (Dset B q i₀)) ^ 2) + K1 * K2 * (ε ^ 2 / (B.m : ℝ) ^ 6) ≤
          (∑ r ∈ fib2 q, (δ₁ (Bset B' r i₀)) ^ 2) +
          (∑ r ∈ fib2 q, (δ₁ (Cset B' r i₀)) ^ 2) +
          (∑ r ∈ fib2 q, (δ₁ (Dset B' r i₀)) ^ 2) := by
        rcases hbig with h1 | h2 | h3
        · have hB0 := (coset_slice_energy_bound hTW q.1 0 (Bset B q i₀)).2 (rOf q) hr_not_ann hT_dot
          rw [le_div_iff₀ hK1] at hB0
          have hB1 : K1 * K2 * ((δ₁ (Bset B q i₀)) ^ 2 + (fhat B.W (Bset B q i₀) (rOf q)) ^ 2) ≤
              ∑ r ∈ fib2 q, (δ₁ (Bset B' r i₀)) ^ 2 := by rw [hB_slice i₀]; nlinarith
          have hsq := mul_le_mul_of_nonneg_left (hsq_lt _ h1) (mul_pos hK1 hK2).le
          have := hC_ge i₀; have := hD_ge i₀
          linarith
        · have hC0 := (coset_slice_energy_bound hTW q.2 0 (Cset B q i₀)).2 (rOf q) hr_not_ann hT_dot
          rw [le_div_iff₀ hK2] at hC0
          have hC1 : K1 * K2 * ((δ₁ (Cset B q i₀)) ^ 2 + (fhat B.W (Cset B q i₀) (rOf q)) ^ 2) ≤
              ∑ r ∈ fib2 q, (δ₁ (Cset B' r i₀)) ^ 2 := by rw [hC_slice i₀]; nlinarith
          have hsq := mul_le_mul_of_nonneg_left (hsq_lt _ h2) (mul_pos hK1 hK2).le
          have := hB_ge i₀; have := hD_ge i₀
          linarith
        · have hD1 : K1 * K2 * ((δ₁ (Dset B q i₀)) ^ 2 + (fhat B.W (Dset B q i₀) (rOf q)) ^ 2) ≤
              ∑ r ∈ fib2 q, (δ₁ (Dset B' r i₀)) ^ 2 := by
            rw [hD_slice i₀]
            calc K1 * K2 * ((δ₁ (Dset B q i₀)) ^ 2 + (fhat B.W (Dset B q i₀) (rOf q)) ^ 2)
                = ∑ _r₁ ∈ fiberQ hTW q.1,
                    (K2 * ((δ₁ (Dset B q i₀)) ^ 2 + (fhat B.W (Dset B q i₀) (rOf q)) ^ 2)) := by
                  simp [Finset.sum_const, nsmul_eq_mul, K1]; ring
              _ ≤ ∑ r₁ ∈ fiberQ hTW q.1, ∑ r₂ ∈ fiberQ hTW q.2,
                    (δ₁ (univ.filter (fun t : T => shiftW hTW r₁ + shiftW hTW r₂ + ⟨t.val, hTW t.prop⟩ ∈ Dset B q i₀))) ^ 2 := by
                  refine sum_le_sum fun r₁ _ => ?_
                  have h := (coset_slice_energy_bound hTW q.2 (shiftW hTW r₁) (Dset B q i₀)).2
                    (rOf q) hr_not_ann hT_dot
                  rw [le_div_iff₀ hK2] at h
                  linarith
          have hsq := mul_le_mul_of_nonneg_left (hsq_lt _ h3) (mul_pos hK1 hK2).le
          have := hB_ge i₀; have := hC_ge i₀
          linarith
      have htot_i : ∑ i : Fin B.m, (K1 * K2 * ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 +
          (δ₁ (Dset B q i)) ^ 2)) + K1 * K2 * (ε ^ 2 / (B.m : ℝ) ^ 6) ≤
          ∑ i : Fin B.m, ((∑ r ∈ fib2 q, (δ₁ (Bset B' r i)) ^ 2) +
            (∑ r ∈ fib2 q, (δ₁ (Cset B' r i)) ^ 2) +
            (∑ r ∈ fib2 q, (δ₁ (Dset B' r i)) ^ 2)) := by
        have hsplit_lhs : ∑ i : Fin B.m, (K1 * K2 * ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 +
            (δ₁ (Dset B q i)) ^ 2)) =
            K1 * K2 * ((δ₁ (Bset B q i₀)) ^ 2 + (δ₁ (Cset B q i₀)) ^ 2 + (δ₁ (Dset B q i₀)) ^ 2) +
            ∑ i ∈ univ.erase i₀, K1 * K2 * ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 + (δ₁ (Dset B q i)) ^ 2) :=
          (Finset.add_sum_erase _ _ (mem_univ i₀)).symm
        have hsplit_rhs : ∑ i : Fin B.m, ((∑ r ∈ fib2 q, (δ₁ (Bset B' r i)) ^ 2) +
            (∑ r ∈ fib2 q, (δ₁ (Cset B' r i)) ^ 2) +
            (∑ r ∈ fib2 q, (δ₁ (Dset B' r i)) ^ 2)) =
            ((∑ r ∈ fib2 q, (δ₁ (Bset B' r i₀)) ^ 2) + (∑ r ∈ fib2 q, (δ₁ (Cset B' r i₀)) ^ 2) +
              (∑ r ∈ fib2 q, (δ₁ (Dset B' r i₀)) ^ 2)) +
            ∑ i ∈ univ.erase i₀, ((∑ r ∈ fib2 q, (δ₁ (Bset B' r i)) ^ 2) +
              (∑ r ∈ fib2 q, (δ₁ (Cset B' r i)) ^ 2) +
              (∑ r ∈ fib2 q, (δ₁ (Dset B' r i)) ^ 2)) :=
          (Finset.add_sum_erase _ _ (mem_univ i₀)).symm
        have hrest : ∑ i ∈ univ.erase i₀, K1 * K2 * ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 + (δ₁ (Dset B q i)) ^ 2) ≤
            ∑ i ∈ univ.erase i₀, ((∑ r ∈ fib2 q, (δ₁ (Bset B' r i)) ^ 2) +
              (∑ r ∈ fib2 q, (δ₁ (Cset B' r i)) ^ 2) +
              (∑ r ∈ fib2 q, (δ₁ (Dset B' r i)) ^ 2)) := by
          refine sum_le_sum fun i _ => ?_
          have := hB_ge i; have := hC_ge i; have := hD_ge i; linarith
        linarith
      unfold E₁_box
      rw [← Finset.mul_sum] at htot_i
      have heq_l : K1 * K2 * ((∑ i : Fin B.m, ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 +
          (δ₁ (Dset B q i)) ^ 2)) / 3 + ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) =
          (K1 * K2 * (∑ i : Fin B.m, ((δ₁ (Bset B q i)) ^ 2 + (δ₁ (Cset B q i)) ^ 2 +
            (δ₁ (Dset B q i)) ^ 2)) + K1 * K2 * (ε ^ 2 / (B.m : ℝ) ^ 6)) / 3 := by ring
      rw [heq_l]
      exact div_le_div_of_nonneg_right htot_i (by norm_num)
    · rw [add_zero]
      unfold E₁_box
      rw [mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      rw [Finset.mul_sum]
      refine sum_le_sum fun i _ => ?_
      have := hB_ge i; have := hC_ge i; have := hD_ge i; linarith
  have hsum_E1 : ∑ q : Q B.W, ((fib2 q).card : ℝ) *
      (E₁_box B q + if q ∈ Bad₁ then ε ^ 2 / (3 * (B.m : ℝ) ^ 6) else 0) ≤
      ∑ r : Q T, E₁_box B' r := by
    calc ∑ q : Q B.W, ((fib2 q).card : ℝ) *
          (E₁_box B q + if q ∈ Bad₁ then ε ^ 2 / (3 * (B.m : ℝ) ^ 6) else 0)
        ≤ ∑ q : Q B.W, ∑ r ∈ fib2 q, E₁_box B' r := sum_le_sum fun q _ => hbox_E1 q
      _ = ∑ r : Q T, E₁_box B' r := by
          have heq : ∀ q : Q B.W, fib2 q =
              univ.filter (fun r : Q T => (Submodule.factor hTW r.1, Submodule.factor hTW r.2) = q) := by
            intro q; ext r; simp [fib2, fiberQ, Prod.ext_iff]
          simp_rw [heq]
          exact Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ)
            (g := fun r : Q T => (Submodule.factor hTW r.1, Submodule.factor hTW r.2))
            (f := fun r : Q T => E₁_box B' r) (fun _ _ => mem_univ _)
  simp_rw [hfib_const, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum_E1
  have hbad_sum : ∑ q : Q B.W, (if q ∈ Bad₁ then ε ^ 2 / (3 * (B.m : ℝ) ^ 6) else 0) =
      (Bad₁.card : ℝ) * (ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) := by
    simp
  rw [hbad_sum] at hsum_E1
  have hbad_ge : ε * (Fintype.card (Q B.W) : ℝ) * (ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) ≤
      (Bad₁.card : ℝ) * (ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) :=
    mul_le_mul_of_nonneg_right hBad_gt.le (by positivity)
  unfold E₁
  change (∑ q : Q B.W, E₁_box B q) / (Fintype.card (Q B.W) : ℝ) + ε ^ 3 / (3 * (B.m : ℝ) ^ 6) ≤
    (∑ r : Q T, E₁_box B' r) / (Fintype.card (Q T) : ℝ)
  have hdiv1 : (∑ q : Q B.W, E₁_box B q) / (Fintype.card (Q B.W) : ℝ) +
      ε ^ 3 / (3 * (B.m : ℝ) ^ 6) =
      ((∑ q : Q B.W, E₁_box B q) + ε * (Fintype.card (Q B.W) : ℝ) *
        (ε ^ 2 / (3 * (B.m : ℝ) ^ 6))) / (Fintype.card (Q B.W) : ℝ) := by
    field_simp [hQW_pos.ne']
  rw [hdiv1, div_le_div_iff₀ hQW_pos hQT_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hQW_pos] at hsum_E1
  have hmul_le : ((∑ q : Q B.W, E₁_box B q) + ε * (Fintype.card (Q B.W) : ℝ) *
      (ε ^ 2 / (3 * (B.m : ℝ) ^ 6))) * (Fintype.card (Q T) : ℝ) ≤
      (Fintype.card (Q T) : ℝ) * ((∑ q : Q B.W, E₁_box B q) +
        (Bad₁.card : ℝ) * (ε ^ 2 / (3 * (B.m : ℝ) ^ 6))) := by
    have hadd : (∑ q : Q B.W, E₁_box B q) + ε * (Fintype.card (Q B.W) : ℝ) *
        (ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) ≤
        (∑ q : Q B.W, E₁_box B q) + (Bad₁.card : ℝ) * (ε ^ 2 / (3 * (B.m : ℝ) ^ 6)) := by linarith
    have hm := mul_le_mul_of_nonneg_left hadd hQT_pos.le
    linarith
  linarith

/-- Refinement (A): when `Cond1` fails, shrinking `W` to `T` increments `E₁` by `ε^3 / (3 * m^6)`,
keeps `m` unchanged, does not decrease `E₂`, and increases `codim` by at most `4^(codim W)`. -/
private lemma refinement_A {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (hfail : ¬ Cond1 ε B) :
    ∃ B' : Boxing n,
      B'.m = B.m ∧
      codim B'.W ≤ codim B.W + 4 ^ codim B.W ∧
      E₂ A B ≤ E₂ A B' ∧
      E₁ B + ε ^ 3 / (3 * (B.m : ℝ) ^ 6) ≤ E₁ B' := by
  let Bad₁ : Finset (Q B.W) := univ.filter (fun q => ¬ BoxUnif ε B q)
  have hBad_gt : ε * (Fintype.card (Q B.W) : ℝ) < (Bad₁.card : ℝ) := by
    unfold Cond1 at hfail; linarith
  have hwit : ∀ q ∈ Bad₁, ∃ r : 𝔽₂ n, r ∉ ann B.W ∧
      ∃ i : Fin B.m,
        ε / (B.m : ℝ) ^ 3 < |fhat B.W (Bset B q i) r| ∨
        ε / (B.m : ℝ) ^ 3 < |fhat B.W (Cset B q i) r| ∨
        ε / (B.m : ℝ) ^ 3 < |fhat B.W (Dset B q i) r| := by
    intro q hq
    have hq' : ¬ BoxUnif ε B q := (Finset.mem_filter.mp hq).2
    unfold BoxUnif at hq'
    push Not at hq'
    rcases hq' with ⟨i, r, hr, hbig⟩
    refine ⟨r, hr, i, ?_⟩
    by_cases h1 : ε / (B.m : ℝ) ^ 3 < |fhat B.W (Bset B q i) r|
    · exact Or.inl h1
    · push Not at h1
      by_cases h2 : ε / (B.m : ℝ) ^ 3 < |fhat B.W (Cset B q i) r|
      · exact Or.inr (Or.inl h2)
      · push Not at h2
        exact Or.inr (Or.inr (hbig h1 h2))
  let rOf : Q B.W → 𝔽₂ n := fun q => if hq : q ∈ Bad₁ then (hwit q hq).choose else 0
  have hfold_props : ∀ S : Finset (Q B.W),
      let M : Submodule (ZMod 2) (𝔽₂ n) := B.W ⊓ ⨅ q ∈ S, LinearMap.ker (dotLM (rOf q))
      M ≤ B.W ∧ (∀ q ∈ S, M ≤ LinearMap.ker (dotLM (rOf q))) ∧
      codim M ≤ codim B.W + S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      dsimp only
      simp
    | @insert q₀ S hq₀ ih =>
      rcases ih with ⟨hleW, hleS, hcod⟩
      have hfold_eq : B.W ⊓ ⨅ q ∈ insert q₀ S, LinearMap.ker (dotLM (rOf q)) =
          (B.W ⊓ ⨅ q ∈ S, LinearMap.ker (dotLM (rOf q))) ⊓ LinearMap.ker (dotLM (rOf q₀)) := by
        apply le_antisymm
        · refine le_inf (le_inf inf_le_left ?_) ?_
          · refine inf_le_right.trans (le_iInf fun q => le_iInf fun hq => ?_)
            exact iInf_le_of_le q (iInf_le _ (Finset.mem_insert_of_mem hq))
          · exact inf_le_right.trans (iInf_le_of_le q₀ (iInf_le _ (Finset.mem_insert_self q₀ S)))
        · refine le_inf (inf_le_left.trans inf_le_left) (le_iInf fun q => le_iInf fun hq => ?_)
          rcases Finset.mem_insert.mp hq with rfl | hqS
          · exact inf_le_right
          · exact (inf_le_left.trans inf_le_right).trans (iInf_le_of_le q (iInf_le _ hqS))
      dsimp only
      rw [hfold_eq]
      refine ⟨inf_le_left.trans hleW, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqS
        · exact inf_le_right
        · exact inf_le_left.trans (hleS q hqS)
      · rw [Finset.card_insert_of_notMem hq₀]
        have hstep := codim_inf_ker_le (B.W ⊓ ⨅ q ∈ S, LinearMap.ker (dotLM (rOf q))) (rOf q₀)
        omega
  rcases hfold_props Bad₁ with ⟨hTW, hTker, hTcod⟩
  have hcard_le : Bad₁.card ≤ 4 ^ codim B.W := by
    rw [← card_Q_eq_four_pow_codim B.W]
    exact Finset.card_le_univ Bad₁
  refine ⟨restrictBoxing B _ hTW, rfl, hTcod.trans (Nat.add_le_add_left hcard_le _),
    E₂_restrictBoxing_ge A B _ hTW, ?_⟩
  refine E₁_restrictBoxing_ge hε B Bad₁ rOf _ hTW hTker hBad_gt fun q hq => ?_
  have hr_eq : rOf q = (hwit q hq).choose := dif_pos hq
  rw [hr_eq]
  exact (hwit q hq).choose_spec

/- ### Refinement (B): refining partitions within each outer box -/

/-- Helper: refining a pair of label maps `(lab1, lab2)` by `(lab1', lab2')` with 2-bit witnesses
increments the sum of `innerTerm` by `ε^4` times the non-quasirandom measure. -/
private lemma refine_pair_innerTerm {n : ℕ} {W : Submodule (ZMod 2) (𝔽₂ n)} {m m' : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (lab1 lab2 : W → Fin m) (lab1' lab2' : W → Fin m')
    (p1 p2 : Fin m' → Fin m)
    (hp1 : ∀ w : W, p1 (lab1' w) = lab1 w)
    (hp2 : ∀ w : W, p2 (lab2' w) = lab2 w)
    (e : W → W → Prop)
    (w1 w2 : Fin m → Fin m → Finset W)
    (hw_sub : ∀ i j, w1 i j ⊆ univ.filter (fun w => lab1 w = i) ∧
      w2 i j ⊆ univ.filter (fun w => lab2 w = j))
    (hw_wit : ∀ i j, ¬ IsQuasirandom ε (univ.filter (fun w => lab1 w = i))
      (univ.filter (fun w => lab2 w = j)) e →
      ε * ((univ.filter (fun w => lab1 w = i)).card : ℝ) ≤ ((w1 i j).card : ℝ) ∧
      ε * ((univ.filter (fun w => lab2 w = j)).card : ℝ) ≤ ((w2 i j).card : ℝ) ∧
      ε < |edgeDens (w1 i j) (w2 i j) e -
        edgeDens (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e|)
    (b1 b2 : Fin m → Fin m' → Bool)
    (hb1 : ∀ i j (w : W), lab1 w = i → b1 j (lab1' w) = decide (w ∈ w1 i j))
    (hb2 : ∀ i j (w : W), lab2 w = j → b2 i (lab2' w) = decide (w ∈ w2 i j)) :
    (∑ i : Fin m, ∑ j : Fin m,
      innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e) +
    ε ^ 4 * (∑ i : Fin m, ∑ j : Fin m,
      if IsQuasirandom ε (univ.filter (fun w => lab1 w = i))
        (univ.filter (fun w => lab2 w = j)) e then 0
      else δ₁ (univ.filter (fun w => lab1 w = i)) * δ₁ (univ.filter (fun w => lab2 w = j))) ≤
    ∑ i' : Fin m', ∑ j' : Fin m',
      innerTerm (univ.filter (fun w => lab1' w = i')) (univ.filter (fun w => lab2' w = j')) e := by
  have hW_pos : (0 : ℝ) < (Fintype.card W : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hW2_pos : (0 : ℝ) < (Fintype.card W : ℝ) ^ 2 := pow_pos hW_pos 2
  let M : Finset (W × W) := univ.filter (fun p : W × W => e p.1 p.2)
  have hblock : ∀ i j : Fin m,
      innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e +
      (if IsQuasirandom ε (univ.filter (fun w => lab1 w = i))
          (univ.filter (fun w => lab2 w = j)) e then 0
       else ε ^ 4 * (δ₁ (univ.filter (fun w => lab1 w = i)) *
         δ₁ (univ.filter (fun w => lab2 w = j)))) ≤
      ∑ i' ∈ univ.filter (fun i' : Fin m' => p1 i' = i),
        ∑ j' ∈ univ.filter (fun j' : Fin m' => p2 j' = j),
          innerTerm (univ.filter (fun w => lab1' w = i')) (univ.filter (fun w => lab2' w = j')) e := by
    intro i j
    let X := univ.filter (fun w : W => lab1 w = i)
    let Y := univ.filter (fun w : W => lab2 w = j)
    let ψ : W × W → Fin m' × Fin m' := fun p => (lab1' p.1, lab2' p.2)
    let φ : W × W → Bool × Bool := fun p => (decide (p.1 ∈ w1 i j), decide (p.2 ∈ w2 i j))
    let proj : Fin m' × Fin m' → Bool × Bool := fun k => (b1 j k.1, b2 i k.2)
    have hproj : ∀ p ∈ X ×ˢ Y, proj (ψ p) = φ p := by
      intro p hp
      simp only [mem_product, X, Y, mem_filter, mem_univ, true_and] at hp
      exact Prod.ext (hb1 i j p.1 hp.1) (hb2 i j p.2 hp.2)
    have href := refinement_energy_mono (X ×ˢ Y) M φ ψ proj hproj
    -- Match the right-hand side of href with |W|^2 * ∑ i' ∈ fib i, ∑ j' ∈ fib j, innerTerm.
    have hrhs : ∑ k : Fin m' × Fin m',
        (((X ×ˢ Y).filter (fun p => ψ p = k)).card : ℝ) *
        (setDens ((X ×ˢ Y).filter (fun p => ψ p = k)) M) ^ 2 =
        (Fintype.card W : ℝ) ^ 2 *
        ∑ i' ∈ univ.filter (fun i' : Fin m' => p1 i' = i),
          ∑ j' ∈ univ.filter (fun j' : Fin m' => p2 j' = j),
            innerTerm (univ.filter (fun w => lab1' w = i'))
              (univ.filter (fun w => lab2' w = j')) e := by
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_subset (Finset.subset_univ (univ.filter (fun i' : Fin m' => p1 i' = i)))]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' hi' => ?_
        simp only [mem_filter, mem_univ, true_and] at hi'
        rw [← Finset.sum_subset (Finset.subset_univ (univ.filter (fun j' : Fin m' => p2 j' = j)))]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' hj' => ?_
          simp only [mem_filter, mem_univ, true_and] at hj'
          have hfilt : (X ×ˢ Y).filter (fun p => ψ p = (i', j')) =
              univ.filter (fun w => lab1' w = i') ×ˢ univ.filter (fun w => lab2' w = j') := by
            ext p
            simp only [mem_filter, mem_product, X, Y, ψ, mem_univ, true_and, Prod.mk.injEq]
            constructor
            · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨⟨by rw [← hp1 p.1, h1, hi'], by rw [← hp2 p.2, h2, hj']⟩, h1, h2⟩
          rw [hfilt, innerTerm_eq_setDens]
          field_simp [hW_pos.ne']
          rfl
        · intro j' _ hj'
          simp only [mem_filter, mem_univ, true_and] at hj'
          have hemp : (X ×ˢ Y).filter (fun p => ψ p = (i', j')) = ∅ := by
            ext p
            simp only [mem_filter, mem_product, X, Y, ψ, mem_univ, true_and, Prod.mk.injEq,
              Finset.notMem_empty, iff_false, not_and]
            rintro ⟨_, h2⟩ _ h2'
            exact hj' (by rw [← h2', hp2 p.2, h2])
          rw [hemp]; simp
      · intro i' _ hi'
        simp only [mem_filter, mem_univ, true_and] at hi'
        refine Finset.sum_eq_zero fun j' _ => ?_
        have hemp : (X ×ˢ Y).filter (fun p => ψ p = (i', j')) = ∅ := by
          ext p
          simp only [mem_filter, mem_product, X, Y, ψ, mem_univ, true_and, Prod.mk.injEq,
            Finset.notMem_empty, iff_false, not_and]
          rintro ⟨h1, _⟩ h1' _
          exact hi' (by rw [← h1', hp1 p.1, h1])
        rw [hemp]; simp
    rw [hrhs] at href
    split_ifs with hqr
    · rw [add_zero]
      have hmono := partition_energy_mono (X ×ˢ Y) M φ
      rw [innerTerm_eq_setDens]
      rw [div_le_iff₀ hW2_pos]
      linarith
    · have hinc := partition_energy_increment (X ×ˢ Y) M φ (true, true)
      have hpiece : (X ×ˢ Y).filter (fun p => φ p = (true, true)) = w1 i j ×ˢ w2 i j := by
        ext p
        simp only [mem_filter, mem_product, φ, Prod.mk.injEq, decide_eq_true_eq]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨(hw_sub i j).1 h1, (hw_sub i j).2 h2⟩, h1, h2⟩
      rw [hpiece] at hinc
      rcases hw_wit i j hqr with ⟨hw1_ge, hw2_ge, hdiff⟩
      have hsd_X : setDens (X ×ˢ Y) M = edgeDens X Y e := by
        rw [edgeDens_eq_setDens]
        unfold setDens
        have hinter : M ∩ (X ×ˢ Y) = (X ×ˢ Y).filter (fun p => e p.1 p.2) ∩ (X ×ˢ Y) := by
          ext p; simp [M, and_comm]
        rw [hinter]
      have hsd_w : setDens (w1 i j ×ˢ w2 i j) M = edgeDens (w1 i j) (w2 i j) e := by
        rw [edgeDens_eq_setDens]
        unfold setDens
        have hinter : M ∩ (w1 i j ×ˢ w2 i j) =
            (w1 i j ×ˢ w2 i j).filter (fun p => e p.1 p.2) ∩ (w1 i j ×ˢ w2 i j) := by
          ext p; simp [M, and_comm]
        rw [hinter]
      rw [hsd_X, hsd_w] at hinc
      have hcard_ge : ε ^ 2 * ((X.card : ℝ) * (Y.card : ℝ)) ≤ ((w1 i j ×ˢ w2 i j).card : ℝ) := by
        rw [Finset.card_product, Nat.cast_mul]
        have h1 := mul_le_mul hw1_ge hw2_ge (mul_nonneg hε.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        linarith
      have hsq_ge : ε ^ 2 ≤ (edgeDens (w1 i j) (w2 i j) e - edgeDens X Y e) ^ 2 := by
        have hsq := pow_le_pow_left₀ hε.le hdiff.le 2
        rw [sq_abs] at hsq; exact hsq
      have hbonus : ε ^ 4 * ((X.card : ℝ) * (Y.card : ℝ)) ≤
          ((w1 i j ×ˢ w2 i j).card : ℝ) * (edgeDens (w1 i j) (w2 i j) e - edgeDens X Y e) ^ 2 := by
        have hm := mul_le_mul hcard_ge hsq_ge (sq_nonneg _) (Nat.cast_nonneg _)
        linarith
      have hLHS : (Fintype.card W : ℝ) ^ 2 *
          (innerTerm X Y e + ε ^ 4 * (δ₁ X * δ₁ Y)) =
          ((X ×ˢ Y).card : ℝ) * (edgeDens X Y e) ^ 2 +
          ε ^ 4 * ((X.card : ℝ) * (Y.card : ℝ)) := by
        unfold innerTerm δ₁
        rw [Finset.card_product, Nat.cast_mul]
        field_simp [hW_pos.ne']
      have htot : (Fintype.card W : ℝ) ^ 2 * (innerTerm X Y e + ε ^ 4 * (δ₁ X * δ₁ Y)) ≤
          (Fintype.card W : ℝ) ^ 2 *
            ∑ i' ∈ univ.filter (fun i' : Fin m' => p1 i' = i),
              ∑ j' ∈ univ.filter (fun j' : Fin m' => p2 j' = j),
                innerTerm (univ.filter (fun w => lab1' w = i'))
                  (univ.filter (fun w => lab2' w = j')) e := by
        linarith
      exact le_of_mul_le_mul_left htot hW2_pos
  -- Sum hblock over all (i, j) : Fin m × Fin m.
  have hsum_ij : (∑ i : Fin m, ∑ j : Fin m,
        innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e) +
      ε ^ 4 * (∑ i : Fin m, ∑ j : Fin m,
        if IsQuasirandom ε (univ.filter (fun w => lab1 w = i))
          (univ.filter (fun w => lab2 w = j)) e then 0
        else δ₁ (univ.filter (fun w => lab1 w = i)) * δ₁ (univ.filter (fun w => lab2 w = j))) =
      ∑ i : Fin m, ∑ j : Fin m,
        (innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e +
          if IsQuasirandom ε (univ.filter (fun w => lab1 w = i))
            (univ.filter (fun w => lab2 w = j)) e then 0
          else ε ^ 4 * (δ₁ (univ.filter (fun w => lab1 w = i)) *
            δ₁ (univ.filter (fun w => lab2 w = j)))) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hsum_ij]
  calc ∑ i : Fin m, ∑ j : Fin m,
        (innerTerm (univ.filter (fun w => lab1 w = i)) (univ.filter (fun w => lab2 w = j)) e +
          if IsQuasirandom ε (univ.filter (fun w => lab1 w = i))
            (univ.filter (fun w => lab2 w = j)) e then 0
          else ε ^ 4 * (δ₁ (univ.filter (fun w => lab1 w = i)) *
            δ₁ (univ.filter (fun w => lab2 w = j))))
      ≤ ∑ i : Fin m, ∑ j : Fin m,
          ∑ i' ∈ univ.filter (fun i' : Fin m' => p1 i' = i),
            ∑ j' ∈ univ.filter (fun j' : Fin m' => p2 j' = j),
              innerTerm (univ.filter (fun w => lab1' w = i'))
                (univ.filter (fun w => lab2' w = j')) e :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hblock i j
    _ = ∑ i : Fin m, ∑ i' ∈ univ.filter (fun i' : Fin m' => p1 i' = i),
          ∑ j : Fin m, ∑ j' ∈ univ.filter (fun j' : Fin m' => p2 j' = j),
            innerTerm (univ.filter (fun w => lab1' w = i'))
              (univ.filter (fun w => lab2' w = j')) e := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin m, ∑ i' ∈ univ.filter (fun i' : Fin m' => p1 i' = i),
          ∑ j' : Fin m',
            innerTerm (univ.filter (fun w => lab1' w = i'))
              (univ.filter (fun w => lab2' w = j')) e := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        exact Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := p2)
          (f := fun j' => innerTerm (univ.filter (fun w => lab1' w = i'))
            (univ.filter (fun w => lab2' w = j')) e) (fun _ _ => mem_univ _)
    _ = ∑ i' : Fin m', ∑ j' : Fin m',
          innerTerm (univ.filter (fun w => lab1' w = i'))
            (univ.filter (fun w => lab2' w = j')) e := by
        exact Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := p1)
          (f := fun i' => ∑ j' : Fin m',
            innerTerm (univ.filter (fun w => lab1' w = i'))
              (univ.filter (fun w => lab2' w = j')) e) (fun _ _ => mem_univ _)

/-- Refinement (B): when `Cond2` fails, refining the inner partitions keeps `W` fixed, increases
`m` to `m * 4^m`, and increments `E₂` by at least `ε^6 / 3`. -/
private lemma refinement_B {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (hfail : ¬ Cond2 ε A B) :
    ∃ B' : Boxing n,
      B'.W = B.W ∧
      B'.m = B.m * 4 ^ B.m ∧
      E₂ A B + ε ^ 6 / 3 ≤ E₂ A B' := by
  let Bad₂ : Finset (Q B.W) := univ.filter (fun q => ¬ BoxQR ε A B q)
  have hBad_gt : ε * (Fintype.card (Q B.W) : ℝ) < (Bad₂.card : ℝ) := by
    unfold Cond2 at hfail; linarith
  -- Witness extractor for non-quasirandom bipartite pairs.
  have hqr_wit : ∀ {X Y : Finset B.W} {e : B.W → B.W → Prop},
      ¬ IsQuasirandom ε X Y e →
      ∃ p : Finset B.W × Finset B.W,
        p.1 ⊆ X ∧ p.2 ⊆ Y ∧
        ε * (X.card : ℝ) ≤ (p.1.card : ℝ) ∧ ε * (Y.card : ℝ) ≤ (p.2.card : ℝ) ∧
        ε < |edgeDens p.1 p.2 e - edgeDens X Y e| := by
    intro X Y e hnot
    unfold IsQuasirandom at hnot
    push Not at hnot
    rcases hnot with ⟨X', hX', Y', hY', h1, h2, h3⟩
    exact ⟨(X', Y'), hX', hY', h1, h2, h3⟩
  let witBC : Q B.W → Fin B.m → Fin B.m → Finset B.W × Finset B.W := fun q i j =>
    if h : ¬ IsQuasirandom ε (Bset B q i) (Cset B q j) (eBC A B.W q) then (hqr_wit h).choose
    else (∅, ∅)
  let witBD : Q B.W → Fin B.m → Fin B.m → Finset B.W × Finset B.W := fun q i k =>
    if h : ¬ IsQuasirandom ε (Bset B q i) (Dset B q k) (eBD A B.W q) then (hqr_wit h).choose
    else (∅, ∅)
  let witCD : Q B.W → Fin B.m → Fin B.m → Finset B.W × Finset B.W := fun q j k =>
    if h : ¬ IsQuasirandom ε (Cset B q j) (Dset B q k) (eCD A B.W q) then (hqr_wit h).choose
    else (∅, ∅)
  let κ := Fin B.m × (Fin B.m → Bool) × (Fin B.m → Bool)
  have hcard_κ : Fintype.card κ = B.m * 4 ^ B.m := by
    dsimp only [κ]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
    rw [← mul_pow]
    norm_num
  have hm'_pos : 0 < B.m * 4 ^ B.m := Nat.mul_pos B.hm (by positivity)
  let eκ : κ ≃ Fin (B.m * 4 ^ B.m) := (Fintype.equivFin κ).trans (finCongr hcard_κ)
  let B' : Boxing n :=
    { W := B.W
      m := B.m * 4 ^ B.m
      hm := hm'_pos
      labB := fun q w => eκ (B.labB q w,
        fun j => decide (w ∈ (witBC q (B.labB q w) j).1),
        fun k => decide (w ∈ (witBD q (B.labB q w) k).1))
      labC := fun q w => eκ (B.labC q w,
        fun i => decide (w ∈ (witBC q i (B.labC q w)).2),
        fun k => decide (w ∈ (witCD q (B.labC q w) k).1))
      labD := fun q w => eκ (B.labD q w,
        fun i => decide (w ∈ (witBD q i (B.labD q w)).2),
        fun j => decide (w ∈ (witCD q j (B.labD q w)).2)) }
  refine ⟨B', rfl, rfl, ?_⟩
  let p : Fin B'.m → Fin B.m := fun idx => (eκ.symm idx).1
  let b1 : Fin B.m → Fin B'.m → Bool := fun j idx => (eκ.symm idx).2.1 j
  let b2 : Fin B.m → Fin B'.m → Bool := fun k idx => (eκ.symm idx).2.2 k
  have hbox_inc : ∀ q : Q B.W,
      E₂_box A B q + (ε ^ 4 / 3) * (badBC ε A B q + badBD ε A B q + badCD ε A B q) ≤
      E₂_box A B' q := by
    intro q
    have hBC := refine_pair_innerTerm hε (B.labB q) (B.labC q) (B'.labB q) (B'.labC q) p p
      (fun w => by simp [B', p]) (fun w => by simp [B', p]) (eBC A B.W q)
      (fun i j => (witBC q i j).1) (fun i j => (witBC q i j).2)
      (fun i j => by
        dsimp only [witBC]
        by_cases h : ¬ IsQuasirandom ε (Bset B q i) (Cset B q j) (eBC A B.W q)
        · rw [dif_pos h]; exact ⟨(hqr_wit h).choose_spec.1, (hqr_wit h).choose_spec.2.1⟩
        · rw [dif_neg h]; exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩)
      (fun i j h => by
        dsimp only [witBC]
        have h' : ¬ IsQuasirandom ε (Bset B q i) (Cset B q j) (eBC A B.W q) := h
        rw [dif_pos h']
        have hs := (hqr_wit h').choose_spec
        exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩)
      b1 b1
      (fun i j w hw => by simp [B', b1, hw])
      (fun i j w hw => by simp [B', b1, hw])
    have hBD := refine_pair_innerTerm hε (B.labB q) (B.labD q) (B'.labB q) (B'.labD q) p p
      (fun w => by simp [B', p]) (fun w => by simp [B', p]) (eBD A B.W q)
      (fun i k => (witBD q i k).1) (fun i k => (witBD q i k).2)
      (fun i k => by
        dsimp only [witBD]
        by_cases h : ¬ IsQuasirandom ε (Bset B q i) (Dset B q k) (eBD A B.W q)
        · rw [dif_pos h]; exact ⟨(hqr_wit h).choose_spec.1, (hqr_wit h).choose_spec.2.1⟩
        · rw [dif_neg h]; exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩)
      (fun i k h => by
        dsimp only [witBD]
        have h' : ¬ IsQuasirandom ε (Bset B q i) (Dset B q k) (eBD A B.W q) := h
        rw [dif_pos h']
        have hs := (hqr_wit h').choose_spec
        exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩)
      b2 b1
      (fun i k w hw => by simp [B', b2, hw])
      (fun i k w hw => by simp [B', b1, hw])
    have hCD := refine_pair_innerTerm hε (B.labC q) (B.labD q) (B'.labC q) (B'.labD q) p p
      (fun w => by simp [B', p]) (fun w => by simp [B', p]) (eCD A B.W q)
      (fun j k => (witCD q j k).1) (fun j k => (witCD q j k).2)
      (fun j k => by
        dsimp only [witCD]
        by_cases h : ¬ IsQuasirandom ε (Cset B q j) (Dset B q k) (eCD A B.W q)
        · rw [dif_pos h]; exact ⟨(hqr_wit h).choose_spec.1, (hqr_wit h).choose_spec.2.1⟩
        · rw [dif_neg h]; exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩)
      (fun j k h => by
        dsimp only [witCD]
        have h' : ¬ IsQuasirandom ε (Cset B q j) (Dset B q k) (eCD A B.W q) := h
        rw [dif_pos h']
        have hs := (hqr_wit h').choose_spec
        exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩)
      b2 b2
      (fun j k w hw => by simp [B', b2, hw])
      (fun j k w hw => by simp [B', b2, hw])
    unfold E₂_box badBC badBD badCD Bset Cset Dset
    simp only [Finset.sum_add_distrib]
    linarith
  -- Sum over all q : Q B.W.
  have hQ_pos : (0 : ℝ) < (Fintype.card (Q B.W) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbad_sum : ε ^ 6 / 3 * (Fintype.card (Q B.W) : ℝ) ≤
      ∑ q : Q B.W, (ε ^ 4 / 3) * (badBC ε A B q + badBD ε A B q + badCD ε A B q) := by
    calc ε ^ 6 / 3 * (Fintype.card (Q B.W) : ℝ)
        = (ε * (Fintype.card (Q B.W) : ℝ)) * (ε ^ 5 / 3) := by ring
      _ ≤ (Bad₂.card : ℝ) * (ε ^ 5 / 3) := mul_le_mul_of_nonneg_right hBad_gt.le (by positivity)
      _ = ∑ _q ∈ Bad₂, (ε ^ 5 / 3) := by simp
      _ ≤ ∑ q ∈ Bad₂, (ε ^ 4 / 3) * (badBC ε A B q + badBD ε A B q + badCD ε A B q) := by
          refine sum_le_sum fun q hq => ?_
          have hq' : ¬ BoxQR ε A B q := (Finset.mem_filter.mp hq).2
          unfold BoxQR at hq'
          have hge : ε ≤ badBC ε A B q + badBD ε A B q + badCD ε A B q := by
            have h01 := badBC_nonneg ε A B q
            have h02 := badBD_nonneg ε A B q
            have h03 := badCD_nonneg ε A B q
            by_contra hlt; push Not at hlt
            exact hq' ⟨by linarith, by linarith, by linarith⟩
          have hmul := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ ε ^ 4 / 3)
          linarith
      _ ≤ ∑ q : Q B.W, (ε ^ 4 / 3) * (badBC ε A B q + badBD ε A B q + badCD ε A B q) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => ?_
          exact mul_nonneg (by positivity)
            (add_nonneg (add_nonneg (badBC_nonneg ε A B q) (badBD_nonneg ε A B q))
              (badCD_nonneg ε A B q))
  have htot : (∑ q : Q B.W, E₂_box A B q) + ε ^ 6 / 3 * (Fintype.card (Q B.W) : ℝ) ≤
      ∑ q : Q B.W, E₂_box A B' q := by
    have h1 := sum_le_sum fun q (_ : q ∈ (univ : Finset (Q B.W))) => hbox_inc q
    rw [Finset.sum_add_distrib] at h1
    linarith
  unfold E₂
  change (∑ q : Q B.W, E₂_box A B q) / (Fintype.card (Q B.W) : ℝ) + ε ^ 6 / 3 ≤
    (∑ q : Q B.W, E₂_box A B' q) / (Fintype.card (Q B.W) : ℝ)
  have hdiv : (∑ q : Q B.W, E₂_box A B q) / (Fintype.card (Q B.W) : ℝ) + ε ^ 6 / 3 =
      ((∑ q : Q B.W, E₂_box A B q) + ε ^ 6 / 3 * (Fintype.card (Q B.W) : ℝ)) /
      (Fintype.card (Q B.W) : ℝ) := by
    field_simp [hQ_pos.ne']
  rw [hdiv]
  exact div_le_div_of_nonneg_right htot hQ_pos.le

/- ### Double induction proving the Regularity Lemma with a uniform codimension bound -/

private lemma regularity_outer {ε : ℝ} (hε : 0 < ε) :
    ∀ (k₂ d m : ℕ), 0 < m →
      ∃ d₀ : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n),
        codim B.W ≤ d → B.m ≤ m → 1 - (k₂ : ℝ) * (ε ^ 6 / 3) ≤ E₂ A B →
        ∃ B' : Boxing n, IsRegular ε A B' ∧ codim B'.W ≤ d₀ := by
  intro k₂
  induction k₂ with
  | zero =>
    intro d m hm
    have hinner : ∀ (k₁ d : ℕ), ∃ d₀ : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n),
        codim B.W ≤ d → B.m ≤ m → 1 ≤ E₂ A B →
        1 - (k₁ : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) ≤ E₁ B →
        ∃ B' : Boxing n, IsRegular ε A B' ∧ codim B'.W ≤ d₀ := by
      intro k₁
      induction k₁ with
      | zero =>
        intro d
        refine ⟨d, fun n A B hcod hBm hE2 hE1 => ?_⟩
        by_cases hC2 : Cond2 ε A B
        · by_cases hC1 : Cond1 ε B
          · exact ⟨B, ⟨hC1, hC2⟩, hcod⟩
          · rcases refinement_A hε A B hC1 with ⟨B₁, _, _, _, hE1'⟩
            have hle := E₁_le_one B₁
            have hpos : (0 : ℝ) < ε ^ 3 / (3 * (B.m : ℝ) ^ 6) := by
              have : (0 : ℝ) < (B.m : ℝ) := Nat.cast_pos.mpr B.hm; positivity
            linarith
        · rcases refinement_B hε A B hC2 with ⟨B₁, _, _, hE2'⟩
          have hle := E₂_le_one A B₁
          have hpos : (0 : ℝ) < ε ^ 6 / 3 := by positivity
          linarith
      | succ k₁ ih₁ =>
        intro d
        rcases ih₁ (d + 4 ^ d) with ⟨dA, hdA⟩
        refine ⟨max d dA, fun n A B hcod hBm hE2 hE1 => ?_⟩
        by_cases hC2 : Cond2 ε A B
        · by_cases hC1 : Cond1 ε B
          · exact ⟨B, ⟨hC1, hC2⟩, hcod.trans (le_max_left _ _)⟩
          · rcases refinement_A hε A B hC1 with ⟨B₁, hBm₁, hcod₁, hE2₁, hE1₁⟩
            have hcod_le : codim B₁.W ≤ d + 4 ^ d := by
              have hpow : 4 ^ codim B.W ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) hcod
              omega
            have hstep_ge : ε ^ 3 / (3 * (m : ℝ) ^ 6) ≤ ε ^ 3 / (3 * (B.m : ℝ) ^ 6) := by
              have hBm_pos : (0 : ℝ) < (B.m : ℝ) := Nat.cast_pos.mpr B.hm
              have hBm_le : (B.m : ℝ) ≤ (m : ℝ) := by exact_mod_cast hBm
              have hpow : (B.m : ℝ) ^ 6 ≤ (m : ℝ) ^ 6 := pow_le_pow_left₀ hBm_pos.le hBm_le 6
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
            have hE1_new : 1 - (k₁ : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) ≤ E₁ B₁ := by
              push_cast at hE1; linarith
            rcases hdA n A B₁ hcod_le (by omega) (hE2.trans hE2₁) hE1_new with ⟨B', hreg, hcod'⟩
            exact ⟨B', hreg, hcod'.trans (le_max_right _ _)⟩
        · rcases refinement_B hε A B hC2 with ⟨B₁, _, _, hE2'⟩
          have hle := E₂_le_one A B₁
          have hpos : (0 : ℝ) < ε ^ 6 / 3 := by positivity
          linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    let k₁ : ℕ := ⌈(3 * (m : ℝ) ^ 6) / ε ^ 3⌉₊
    rcases hinner k₁ d with ⟨d₀, hd₀⟩
    refine ⟨d₀, fun n A B hcod hBm hE2 => hd₀ n A B hcod hBm (by simpa using hE2) ?_⟩
    have hk₁ : (3 * (m : ℝ) ^ 6) / ε ^ 3 ≤ (k₁ : ℝ) := Nat.le_ceil _
    have hmul : (1 : ℝ) ≤ (k₁ : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) := by
      have hpos : (0 : ℝ) < ε ^ 3 / (3 * (m : ℝ) ^ 6) := by positivity
      have h1 := mul_le_mul_of_nonneg_right hk₁ hpos.le
      have h2 : (3 * (m : ℝ) ^ 6) / ε ^ 3 * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) = 1 := by
        field_simp [hε.ne', hm_pos.ne']
      linarith
    linarith [E₁_nonneg B]
  | succ k₂ ih₂ =>
    intro d m hm
    have hinner : ∀ (k₁ d : ℕ), ∃ d₀ : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n),
        codim B.W ≤ d → B.m ≤ m →
        1 - ((k₂ + 1 : ℕ) : ℝ) * (ε ^ 6 / 3) ≤ E₂ A B →
        1 - (k₁ : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) ≤ E₁ B →
        ∃ B' : Boxing n, IsRegular ε A B' ∧ codim B'.W ≤ d₀ := by
      intro k₁
      induction k₁ with
      | zero =>
        intro d
        rcases ih₂ d (m * 4 ^ m) (Nat.mul_pos hm (by positivity)) with ⟨dB, hdB⟩
        refine ⟨max d dB, fun n A B hcod hBm hE2 hE1 => ?_⟩
        by_cases hC2 : Cond2 ε A B
        · by_cases hC1 : Cond1 ε B
          · exact ⟨B, ⟨hC1, hC2⟩, hcod.trans (le_max_left _ _)⟩
          · rcases refinement_A hε A B hC1 with ⟨B₁, _, _, _, hE1'⟩
            have hle := E₁_le_one B₁
            have hpos : (0 : ℝ) < ε ^ 3 / (3 * (B.m : ℝ) ^ 6) := by
              have : (0 : ℝ) < (B.m : ℝ) := Nat.cast_pos.mpr B.hm; positivity
            simp only [Nat.cast_zero, zero_mul, sub_zero] at hE1
            linarith
        · rcases refinement_B hε A B hC2 with ⟨B₁, hW₁, hm₁, hE2₁⟩
          have hcod₁ : codim B₁.W ≤ d := by rw [hW₁]; exact hcod
          have hm₁_le : B₁.m ≤ m * 4 ^ m := by
            rw [hm₁]
            exact Nat.mul_le_mul hBm (Nat.pow_le_pow_right (by norm_num) hBm)
          have hE2_new : 1 - (k₂ : ℝ) * (ε ^ 6 / 3) ≤ E₂ A B₁ := by
            push_cast at hE2; linarith
          rcases hdB n A B₁ hcod₁ hm₁_le hE2_new with ⟨B', hreg, hcod'⟩
          exact ⟨B', hreg, hcod'.trans (le_max_right _ _)⟩
      | succ k₁ ih₁ =>
        intro d
        rcases ih₂ d (m * 4 ^ m) (Nat.mul_pos hm (by positivity)) with ⟨dB, hdB⟩
        rcases ih₁ (d + 4 ^ d) with ⟨dA, hdA⟩
        refine ⟨max d (max dB dA), fun n A B hcod hBm hE2 hE1 => ?_⟩
        by_cases hC2 : Cond2 ε A B
        · by_cases hC1 : Cond1 ε B
          · exact ⟨B, ⟨hC1, hC2⟩, hcod.trans (le_max_left _ _)⟩
          · rcases refinement_A hε A B hC1 with ⟨B₁, hBm₁, hcod₁, hE2₁, hE1₁⟩
            have hcod_le : codim B₁.W ≤ d + 4 ^ d := by
              have hpow : 4 ^ codim B.W ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) hcod
              omega
            have hstep_ge : ε ^ 3 / (3 * (m : ℝ) ^ 6) ≤ ε ^ 3 / (3 * (B.m : ℝ) ^ 6) := by
              have hBm_pos : (0 : ℝ) < (B.m : ℝ) := Nat.cast_pos.mpr B.hm
              have hBm_le : (B.m : ℝ) ≤ (m : ℝ) := by exact_mod_cast hBm
              have hpow : (B.m : ℝ) ^ 6 ≤ (m : ℝ) ^ 6 := pow_le_pow_left₀ hBm_pos.le hBm_le 6
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
            have hE1_new : 1 - (k₁ : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) ≤ E₁ B₁ := by
              push_cast at hE1; linarith
            rcases hdA n A B₁ hcod_le (by omega) (hE2.trans hE2₁) hE1_new with ⟨B', hreg, hcod'⟩
            exact ⟨B', hreg, hcod'.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
        · rcases refinement_B hε A B hC2 with ⟨B₁, hW₁, hm₁, hE2₁⟩
          have hcod₁ : codim B₁.W ≤ d := by rw [hW₁]; exact hcod
          have hm₁_le : B₁.m ≤ m * 4 ^ m := by
            rw [hm₁]
            exact Nat.mul_le_mul hBm (Nat.pow_le_pow_right (by norm_num) hBm)
          have hE2_new : 1 - (k₂ : ℝ) * (ε ^ 6 / 3) ≤ E₂ A B₁ := by
            push_cast at hE2; linarith
          rcases hdB n A B₁ hcod₁ hm₁_le hE2_new with ⟨B', hreg, hcod'⟩
          exact ⟨B', hreg, hcod'.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    let k₁ : ℕ := ⌈(3 * (m : ℝ) ^ 6) / ε ^ 3⌉₊
    rcases hinner k₁ d with ⟨d₀, hd₀⟩
    refine ⟨d₀, fun n A B hcod hBm hE2 => hd₀ n A B hcod hBm hE2 ?_⟩
    have hk₁ : (3 * (m : ℝ) ^ 6) / ε ^ 3 ≤ (k₁ : ℝ) := Nat.le_ceil _
    have hmul : (1 : ℝ) ≤ (k₁ : ℝ) * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) := by
      have hpos : (0 : ℝ) < ε ^ 3 / (3 * (m : ℝ) ^ 6) := by positivity
      have h1 := mul_le_mul_of_nonneg_right hk₁ hpos.le
      have h2 : (3 * (m : ℝ) ^ 6) / ε ^ 3 * (ε ^ 3 / (3 * (m : ℝ) ^ 6)) = 1 := by
        field_simp [hε.ne', hm_pos.ne']
      linarith
    linarith [E₁_nonneg B]

/-- Mandache Regularity Lemma on `𝔽₂ n` with codimension bound independent of `n` and `A`. -/
private lemma regularity_lemma {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)),
      ∃ B : Boxing n, IsRegular ε A B ∧ codim B.W ≤ d₀ := by
  let k₂ : ℕ := ⌈(3 : ℝ) / ε ^ 6⌉₊
  rcases regularity_outer hε k₂ 0 1 (by norm_num) with ⟨d₀, hd₀⟩
  refine ⟨d₀, fun n A => ?_⟩
  let B₀ : Boxing n :=
    { W := ⊤
      m := 1
      hm := by norm_num
      labB := fun _ _ => 0
      labC := fun _ _ => 0
      labD := fun _ _ => 0 }
  have hcod0 : codim B₀.W = 0 := by
    have h1 := codim_add_finrank B₀.W
    have h2 : Module.finrank (ZMod 2) B₀.W = n := by
      dsimp only [B₀]
      rw [finrank_top]
      simp [𝔽₂, 𝔽]
    omega
  have hk₂ : (3 : ℝ) / ε ^ 6 ≤ (k₂ : ℝ) := Nat.le_ceil _
  have hmul : (1 : ℝ) ≤ (k₂ : ℝ) * (ε ^ 6 / 3) := by
    have hpos : (0 : ℝ) < ε ^ 6 / 3 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hk₂ hpos.le
    have h2 : (3 : ℝ) / ε ^ 6 * (ε ^ 6 / 3) = 1 := by field_simp [hε.ne']
    linarith
  exact hd₀ n A B₀ (by omega) le_rfl (by linarith [E₂_nonneg A B₀])

end Regularity

/- ## Section 5: Regular Outer Box Corner Count -/

section BoxCounting

/-- Number of corners inside outer box `q`. -/
private noncomputable def cornersBox {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) (q : Q W) : ℕ :=
  (univ.filter (fun t : W × W × W =>
    eBC A W q t.1 t.2.1 ∧ eBD A W q t.1 t.2.2 ∧ eCD A W q t.2.1 t.2.2)).card

/-- Density of `A` inside outer box `q`. -/
private noncomputable def alphaBox {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) (q : Q W) : ℝ :=
  ((A_box A W q).card : ℝ) / (Fintype.card W : ℝ) ^ 2

private lemma alphaBox_nonneg {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) (q : Q W) : 0 ≤ alphaBox A W q := by
  unfold alphaBox; positivity

private lemma alphaBox_le_one {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) (q : Q W) : alphaBox A W q ≤ 1 := by
  unfold alphaBox
  have hW2 : (0 : ℝ) < (Fintype.card W : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) 2
  rw [div_le_one hW2]
  have hle : (A_box A W q).card ≤ Fintype.card (W × W) := Finset.card_le_univ _
  rw [Fintype.card_prod] at hle
  have hcast : ((A_box A W q).card : ℝ) ≤ (Fintype.card W : ℝ) * (Fintype.card W : ℝ) := by
    exact_mod_cast hle
  linarith

/-- Step 1 of box counting: triangle counting lower bound on `cornersBox`. -/
private lemma cornersBox_ge_triforce_sum
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (q : Q B.W)
    (hQR : BoxQR ε A B q) :
    (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      edgeDens (Bset B q i) (Cset B q j) (eBC A B.W q) *
      edgeDens (Bset B q i) (Dset B q k) (eBD A B.W q) *
      edgeDens (Cset B q j) (Dset B q k) (eCD A B.W q) *
      ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)) -
    8 * ε * (Fintype.card B.W : ℝ) ^ 3 ≤ (cornersBox A B.W q : ℝ) := by
  set w : ℝ := (Fintype.card B.W : ℝ)
  have hw_pos : 0 < w := Nat.cast_pos.mpr Fintype.card_pos
  have hdecomp : (cornersBox A B.W q : ℝ) =
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (((Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter
          (fun t => eBC A B.W q t.1 t.2.1 ∧ eBD A B.W q t.1 t.2.2 ∧ eCD A B.W q t.2.1 t.2.2)).card : ℝ) := by
    have hnat : cornersBox A B.W q =
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          ((Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter
            (fun t => eBC A B.W q t.1 t.2.1 ∧ eBD A B.W q t.1 t.2.2 ∧ eCD A B.W q t.2.1 t.2.2)).card := by
      let S := univ.filter (fun t : B.W × B.W × B.W =>
        eBC A B.W q t.1 t.2.1 ∧ eBD A B.W q t.1 t.2.2 ∧ eCD A B.W q t.2.1 t.2.2)
      have hcard_eq : ∀ i j k : Fin B.m,
          ((Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter
            (fun t => eBC A B.W q t.1 t.2.1 ∧ eBD A B.W q t.1 t.2.2 ∧ eCD A B.W q t.2.1 t.2.2)).card =
          (S.filter (fun t => B.labB q t.1 = i ∧ B.labC q t.2.1 = j ∧ B.labD q t.2.2 = k)).card := by
        intro i j k; congr 1; ext t
        simp [S, Bset, Cset, Dset, and_comm, and_assoc]
      change S.card = _
      simp_rw [hcard_eq, Finset.card_filter]
      calc S.card = ∑ _t ∈ S, (1 : ℕ) := by simp
        _ = ∑ t ∈ S, ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
              if B.labB q t.1 = i ∧ B.labC q t.2.1 = j ∧ B.labD q t.2.2 = k then 1 else 0 := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.sum_eq_single (B.labB q t.1)]
            · rw [Finset.sum_eq_single (B.labC q t.2.1)]
              · rw [Finset.sum_eq_single (B.labD q t.2.2)]
                · simp
                · intro k _ hk; simp [hk.symm]
                · intro h; exact absurd (mem_univ _) h
              · intro j _ hj; refine Finset.sum_eq_zero fun k _ => ?_; simp [hj.symm]
              · intro h; exact absurd (mem_univ _) h
            · intro i _ hi
              refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
              simp [hi.symm]
            · intro h; exact absurd (mem_univ _) h
        _ = ∑ i : Fin B.m, ∑ t ∈ S, ∑ j : Fin B.m, ∑ k : Fin B.m,
              if B.labB q t.1 = i ∧ B.labC q t.2.1 = j ∧ B.labD q t.2.2 = k then 1 else 0 := by
            rw [Finset.sum_comm]
        _ = ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ t ∈ S, ∑ k : Fin B.m,
              if B.labB q t.1 = i ∧ B.labC q t.2.1 = j ∧ B.labD q t.2.2 = k then 1 else 0 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, ∑ t ∈ S,
              if B.labB q t.1 = i ∧ B.labC q t.2.1 = j ∧ B.labD q t.2.2 = k then 1 else 0 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    exact_mod_cast hnat
  let dBC (i j : Fin B.m) : ℝ := edgeDens (Bset B q i) (Cset B q j) (eBC A B.W q)
  let dBD (i k : Fin B.m) : ℝ := edgeDens (Bset B q i) (Dset B q k) (eBD A B.W q)
  let dCD (j k : Fin B.m) : ℝ := edgeDens (Cset B q j) (Dset B q k) (eCD A B.W q)
  let flBC (i j : Fin B.m) : ℝ := if IsQuasirandom ε (Bset B q i) (Cset B q j) (eBC A B.W q) then 0 else 1
  let flBD (i k : Fin B.m) : ℝ := if IsQuasirandom ε (Bset B q i) (Dset B q k) (eBD A B.W q) then 0 else 1
  let flCD (j k : Fin B.m) : ℝ := if IsQuasirandom ε (Cset B q j) (Dset B q k) (eCD A B.W q) then 0 else 1
  have hd_prod_le : ∀ i j k : Fin B.m, dBC i j * dBD i k * dCD j k ≤ 1 := by
    intro i j k
    have h10 := edgeDens_nonneg (Bset B q i) (Cset B q j) (eBC A B.W q)
    have h11 := edgeDens_le_one (Bset B q i) (Cset B q j) (eBC A B.W q)
    have h20 := edgeDens_nonneg (Bset B q i) (Dset B q k) (eBD A B.W q)
    have h21 := edgeDens_le_one (Bset B q i) (Dset B q k) (eBD A B.W q)
    have h30 := edgeDens_nonneg (Cset B q j) (Dset B q k) (eCD A B.W q)
    have h31 := edgeDens_le_one (Cset B q j) (Dset B q k) (eCD A B.W q)
    have h12 : dBC i j * dBD i k ≤ 1 := by nlinarith
    nlinarith
  have htri_each : ∀ i j k : Fin B.m,
      (dBC i j * dBD i k * dCD j k - 5 * ε - (flBC i j + flBD i k + flCD j k)) *
        ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) ≤
      (((Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter
        (fun t => eBC A B.W q t.1 t.2.1 ∧ eBD A B.W q t.1 t.2.2 ∧ eCD A B.W q t.2.1 t.2.2)).card : ℝ) := by
    intro i j k
    by_cases h1 : IsQuasirandom ε (Bset B q i) (Cset B q j) (eBC A B.W q)
    · by_cases h2 : IsQuasirandom ε (Bset B q i) (Dset B q k) (eBD A B.W q)
      · by_cases h3 : IsQuasirandom ε (Cset B q j) (Dset B q k) (eCD A B.W q)
        · simp only [flBC, flBD, flCD, h1, h2, h3, if_true, add_zero, sub_zero]
          exact triangle_counting_lemma hε (Bset B q i) (Cset B q j) (Dset B q k)
            (eBC A B.W q) (eBD A B.W q) (eCD A B.W q) h1 h2 h3
        · have hfl : 1 ≤ flBC i j + flBD i k + flCD j k := by simp [flBC, flBD, flCD, h1, h2, h3]
          have hneg : dBC i j * dBD i k * dCD j k - 5 * ε - (flBC i j + flBD i k + flCD j k) ≤ 0 := by
            linarith [hd_prod_le i j k]
          exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg hneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
            (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)
      · have hfl : 1 ≤ flBC i j + flBD i k + flCD j k := by
          dsimp only [flBC, flBD, flCD]; rw [if_pos h1, if_neg h2]; split_ifs <;> norm_num
        have hneg : dBC i j * dBD i k * dCD j k - 5 * ε - (flBC i j + flBD i k + flCD j k) ≤ 0 := by
          linarith [hd_prod_le i j k]
        exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)
    · have hfl : 1 ≤ flBC i j + flBD i k + flCD j k := by
        dsimp only [flBC, flBD, flCD]; rw [if_neg h1]; split_ifs <;> norm_num
      have hneg : dBC i j * dBD i k * dCD j k - 5 * ε - (flBC i j + flBD i k + flCD j k) ≤ 0 := by
        linarith [hd_prod_le i j k]
      exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)
  have hsumB : ∑ i : Fin B.m, ((Bset B q i).card : ℝ) = w := by
    have h := sum_δ₁_label (B.labB q)
    unfold δ₁ at h; rw [← Finset.sum_div, div_eq_one_iff_eq hw_pos.ne'] at h
    exact h
  have hsumC : ∑ j : Fin B.m, ((Cset B q j).card : ℝ) = w := by
    have h := sum_δ₁_label (B.labC q)
    unfold δ₁ at h; rw [← Finset.sum_div, div_eq_one_iff_eq hw_pos.ne'] at h
    exact h
  have hsumD : ∑ k : Fin B.m, ((Dset B q k).card : ℝ) = w := by
    have h := sum_δ₁_label (B.labD q)
    unfold δ₁ at h; rw [← Finset.sum_div, div_eq_one_iff_eq hw_pos.ne'] at h
    exact h
  have hsum_flBC : ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      flBC i j * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
      badBC ε A B q * w ^ 3 := by
    have h1 : ∀ i j : Fin B.m, ∑ k : Fin B.m,
        flBC i j * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
        flBC i j * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * w := fun i j => by
      rw [← Finset.mul_sum, hsumD]
    simp_rw [h1]
    unfold badBC δ₁
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [flBC, w]; split_ifs <;> (field_simp [hw_pos.ne']; try ring)
  have hsum_flBD : ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      flBD i k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
      badBD ε A B q * w ^ 3 := by
    have h1 : ∀ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        flBD i k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
        ∑ k : Fin B.m, flBD i k * ((Bset B q i).card : ℝ) * ((Dset B q k).card : ℝ) * w := by
      intro i; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc ∑ j : Fin B.m, flBD i k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)
          = ∑ j : Fin B.m, (flBD i k * ((Bset B q i).card : ℝ) * ((Dset B q k).card : ℝ)) * ((Cset B q j).card : ℝ) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = flBD i k * ((Bset B q i).card : ℝ) * ((Dset B q k).card : ℝ) * w := by
            rw [← Finset.mul_sum, hsumC]
    simp_rw [h1]
    unfold badBD δ₁
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [flBD, w]; split_ifs <;> (field_simp [hw_pos.ne']; try ring)
  have hsum_flCD : ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      flCD j k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
      badCD ε A B q * w ^ 3 := by
    rw [Finset.sum_comm]
    have h1 : ∀ j : Fin B.m, ∑ i : Fin B.m, ∑ k : Fin B.m,
        flCD j k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
        ∑ k : Fin B.m, flCD j k * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) * w := by
      intro j; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc ∑ i : Fin B.m, flCD j k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)
          = ∑ i : Fin B.m, (flCD j k * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)) * ((Bset B q i).card : ℝ) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = flCD j k * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) * w := by
            rw [← Finset.mul_sum, hsumB]
    simp_rw [h1]
    unfold badCD δ₁
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [flCD, w]; split_ifs <;> (field_simp [hw_pos.ne']; try ring)
  have hsum_const : ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      (5 * ε) * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
      5 * ε * w ^ 3 := by
    have h1 : ∀ i j : Fin B.m, ∑ k : Fin B.m,
        (5 * ε) * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
        (5 * ε) * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * w := fun i j => by
      rw [← Finset.mul_sum, hsumD]
    simp_rw [h1]
    have h2 : ∀ i : Fin B.m, ∑ j : Fin B.m,
        (5 * ε) * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * w =
        (5 * ε) * ((Bset B q i).card : ℝ) * w * w := fun i => by
      calc ∑ j : Fin B.m, (5 * ε) * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * w
          = ∑ j : Fin B.m, ((5 * ε) * ((Bset B q i).card : ℝ) * w) * ((Cset B q j).card : ℝ) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = (5 * ε) * ((Bset B q i).card : ℝ) * w * w := by rw [← Finset.mul_sum, hsumC]
    simp_rw [h2]
    calc ∑ i : Fin B.m, (5 * ε) * ((Bset B q i).card : ℝ) * w * w
        = ∑ i : Fin B.m, ((5 * ε) * w * w) * ((Bset B q i).card : ℝ) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (5 * ε) * w * w * w := by rw [← Finset.mul_sum, hsumB]
      _ = 5 * ε * w ^ 3 := by ring
  have hsum := sum_le_sum fun i (_ : i ∈ univ) => sum_le_sum fun j (_ : j ∈ univ) =>
    sum_le_sum fun k (_ : k ∈ univ) => htri_each i j k
  rw [← hdecomp] at hsum
  have hsub : ∀ i j k : Fin B.m,
      (dBC i j * dBD i k * dCD j k - 5 * ε - (flBC i j + flBD i k + flCD j k)) *
        ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) =
      dBC i j * dBD i k * dCD j k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) -
      5 * ε * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) -
      (flBC i j * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) +
       flBD i k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) +
       flCD j k * ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)) := by
    intro i j k; ring
  simp_rw [hsub, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hsum_const, hsum_flBC, hsum_flBD, hsum_flCD] at hsum
  rcases hQR with ⟨hqr1, hqr2, hqr3⟩
  have hbad3 : (badBC ε A B q + badBD ε A B q + badCD ε A B q) * w ^ 3 ≤ 3 * ε * w ^ 3 := by
    have hadd : badBC ε A B q + badBD ε A B q + badCD ε A B q ≤ 3 * ε := by linarith
    have hm := mul_le_mul_of_nonneg_right hadd (pow_nonneg hw_pos.le 3)
    linarith
  linarith

/-- Step 2 of box counting: weighted triforce lower bound on the main term using Fourier uniformity. -/
private lemma triforce_sum_ge_weighted
    {c b ε : ℝ} (hc : 1 ≤ c) (hb : 0 < b) (hε : 0 < ε)
    (hH : ∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
      let xy (e : Fin q × Fin q × Fin q) := (e.1, e.2.1)
      let xz (e : Fin q × Fin q × Fin q) := (e.1, e.2.2)
      let yz (e : Fin q × Fin q × Fin q) := (e.2.1, e.2.2)
      let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
        (H.filter (fun e => proj e = x)).card
      let density : ℝ := H.card / (q : ℝ) ^ 3
      let triforce := (∑ e : Fin q × Fin q × Fin q,
        deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q : ℝ) ^ 6
      b * density ^ c ≤ triforce)
    {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (q : Q B.W)
    (hUnif : BoxUnif ε B q) :
    b * (max 0 (alphaBox A B.W q - ε)) ^ c * (Fintype.card B.W : ℝ) ^ 3 ≤
    ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
      edgeDens (Bset B q i) (Cset B q j) (eBC A B.W q) *
      edgeDens (Bset B q i) (Dset B q k) (eBD A B.W q) *
      edgeDens (Cset B q j) (Dset B q k) (eCD A B.W q) *
      ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) := by
  set w : ℝ := (Fintype.card B.W : ℝ)
  have hw_pos : 0 < w := Nat.cast_pos.mpr Fintype.card_pos
  have hw3_pos : 0 < w ^ 3 := pow_pos hw_pos 3
  let dBC (i j : Fin B.m) : ℝ := edgeDens (Bset B q i) (Cset B q j) (eBC A B.W q)
  let dBD (i k : Fin B.m) : ℝ := edgeDens (Bset B q i) (Dset B q k) (eBD A B.W q)
  let dCD (j k : Fin B.m) : ℝ := edgeDens (Cset B q j) (Dset B q k) (eCD A B.W q)
  set Tmain : ℝ := ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
    dBC i j * dBD i k * dCD j k *
      ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)
  -- Step 2: Construct weighted function f' and truncated f = min f' 1 on B.W^3.
  let Pcnt (i j k : Fin B.m) : ℕ :=
    ((Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter
      (fun t => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A_box A B.W q)).card
  let val' (i j k : Fin B.m) : ℝ :=
    if (Bset B q i).card = 0 ∨ (Cset B q j).card = 0 ∨ (Dset B q k).card = 0 then 0
    else (Pcnt i j k : ℝ) * w /
      (((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ))
  have hval'_nonneg : ∀ i j k, 0 ≤ val' i j k := fun i j k => by
    dsimp only [val']; split_ifs
    · exact le_rfl
    · positivity
  have hval'_mul : ∀ i j k,
      ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) * val' i j k =
      (Pcnt i j k : ℝ) * w := by
    intro i j k
    dsimp only [val']
    split_ifs with h0
    · have hP0 : Pcnt i j k = 0 := by
        have hle : Pcnt i j k ≤ (Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        rw [Finset.card_product, Finset.card_product] at hle
        rcases h0 with h | h | h <;> simp [h] at hle <;> exact hle
      rcases h0 with h | h | h <;> simp [h, hP0]
    · push Not at h0
      have h1 : ((Bset B q i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.1
      have h2 : ((Cset B q j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.2.1
      have h3 : ((Dset B q k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.2.2
      field_simp [h1, h2, h3]
  let f' : B.W → B.W → B.W → ℝ := fun a b c => val' (B.labB q a) (B.labC q b) (B.labD q c)
  let f : B.W → B.W → B.W → ℝ := fun a b c => min (f' a b c) 1
  have hf0 : ∀ a b c, 0 ≤ f a b c := fun a b c => le_min (hval'_nonneg _ _ _) zero_le_one
  have hf1 : ∀ a b c, f a b c ≤ 1 := fun a b c => min_le_right _ _
  have hf_le_f' : ∀ a b c, f a b c ≤ f' a b c := fun a b c => min_le_left _ _
  -- Group sums over B.W by labels.
  have hsum_by_lab : ∀ (g : Fin B.m → Fin B.m → Fin B.m → ℝ),
      ∑ a : B.W, ∑ b : B.W, ∑ c : B.W, g (B.labB q a) (B.labC q b) (B.labD q c) =
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) * g i j k := by
    intro g
    have hlab : ∀ (lab : B.W → Fin B.m) (h : Fin B.m → ℝ),
        ∑ x : B.W, h (lab x) = ∑ i : Fin B.m, ((univ.filter (fun x : B.W => lab x = i)).card : ℝ) * h i := by
      intro lab h
      rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := lab)
        (f := fun x => h (lab x)) (fun _ _ => mem_univ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcongr : ∀ x ∈ univ.filter (fun x : B.W => lab x = i), h (lab x) = h i := fun x hx => by
        rw [(Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
    have hstep1 : ∀ a b : B.W, ∑ c : B.W, g (B.labB q a) (B.labC q b) (B.labD q c) =
        ∑ k : Fin B.m, ((Dset B q k).card : ℝ) * g (B.labB q a) (B.labC q b) k := fun a b =>
      hlab (B.labD q) (fun k => g (B.labB q a) (B.labC q b) k)
    have hstep2 : ∀ a : B.W, ∑ b : B.W, ∑ k : Fin B.m, ((Dset B q k).card : ℝ) * g (B.labB q a) (B.labC q b) k =
        ∑ j : Fin B.m, ((Cset B q j).card : ℝ) * ∑ k : Fin B.m, ((Dset B q k).card : ℝ) * g (B.labB q a) j k :=
      fun a => hlab (B.labC q) (fun j => ∑ k : Fin B.m, ((Dset B q k).card : ℝ) * g (B.labB q a) j k)
    simp_rw [hstep1, hstep2]
    rw [hlab (B.labB q) (fun i => ∑ j : Fin B.m, ((Cset B q j).card : ℝ) *
      ∑ k : Fin B.m, ((Dset B q k).card : ℝ) * g i j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [Bset, Cset, Dset]; ring
  -- Marginals of f'.
  have hmarg_xy : ∀ a b : B.W, ∑ c : B.W, f' a b c = w * dBC (B.labB q a) (B.labC q b) := by
    intro a b
    set i := B.labB q a
    set j := B.labC q b
    have ha : a ∈ Bset B q i := Finset.mem_filter.mpr ⟨mem_univ a, rfl⟩
    have hb_mem : b ∈ Cset B q j := Finset.mem_filter.mpr ⟨mem_univ b, rfl⟩
    have hBi_ne : (Bset B q i).card ≠ 0 := (Finset.card_pos.mpr ⟨a, ha⟩).ne'
    have hCj_ne : (Cset B q j).card ≠ 0 := (Finset.card_pos.mpr ⟨b, hb_mem⟩).ne'
    have hBi_r : ((Bset B q i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hBi_ne
    have hCj_r : ((Cset B q j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hCj_ne
    have hsum_c : ∑ c : B.W, f' a b c = ∑ k : Fin B.m, ((Dset B q k).card : ℝ) * val' i j k := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := B.labD q)
        (f := fun c => f' a b c) (fun _ _ => mem_univ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      change ∑ c ∈ Dset B q k, f' a b c = ((Dset B q k).card : ℝ) * val' i j k
      have hc : ∀ c ∈ Dset B q k, f' a b c = val' i j k := fun c hc => by
        dsimp only [f']; rw [(Finset.mem_filter.mp hc).2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_c]
    have hterm : ∀ k : Fin B.m, ((Dset B q k).card : ℝ) * val' i j k =
        (Pcnt i j k : ℝ) * w / (((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ)) := by
      intro k
      have hm := hval'_mul i j k
      rw [eq_div_iff (mul_ne_zero hBi_r hCj_r)]
      linarith
    simp_rw [hterm, ← Finset.sum_div, ← Finset.sum_mul]
    have hsumP : ∑ k : Fin B.m, (Pcnt i j k : ℝ) =
        (((Bset B q i ×ˢ Cset B q j).filter (fun p => eBC A B.W q p.1 p.2)).card : ℝ) := by
      have hnat : ∑ k : Fin B.m, Pcnt i j k =
          ((Bset B q i ×ˢ Cset B q j).filter (fun p => eBC A B.W q p.1 p.2)).card := by
        have h1 : ∀ k : Fin B.m, Pcnt i j k =
            (((Bset B q i ×ˢ Cset B q j).filter (fun p => eBC A B.W q p.1 p.2)).filter
              (fun p => B.labD q (p.1 + p.2) = k)).card := by
          intro k
          refine Finset.card_bij (fun t _ => (t.1, t.2.1)) ?_ ?_ ?_
          · intro t ht
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
            rcases ht with ⟨⟨hB, hC, hD⟩, hsum0, hA⟩
            have hc_eq : t.1 + t.2.1 = t.2.2 := by
              apply Subtype.ext
              have hv : t.1.val + t.2.1.val + t.2.2.val = 0 := congrArg Subtype.val hsum0
              calc t.1.val + t.2.1.val
                  = (t.1.val + t.2.1.val + t.2.2.val) + t.2.2.val := by
                    rw [add_assoc, f2_add_self, add_zero]
                _ = t.2.2.val := by rw [hv, zero_add]
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨⟨hB, hC⟩, hA⟩, by rw [hc_eq]; exact (Finset.mem_filter.mp hD).2⟩
          · intro t₁ ht₁ t₂ ht₂ heq
            have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            simp only [mem_filter] at ht₁ ht₂
            have h3 : t₁.2.2 = t₂.2.2 := by
              apply Subtype.ext
              have hv1 : t₁.1.val + t₁.2.1.val + t₁.2.2.val = 0 := congrArg Subtype.val ht₁.2.1
              have hv2 : t₂.1.val + t₂.2.1.val + t₂.2.2.val = 0 := congrArg Subtype.val ht₂.2.1
              have h1v : t₁.1.val = t₂.1.val := congrArg Subtype.val h1
              have h2v : t₁.2.1.val = t₂.2.1.val := congrArg Subtype.val h2
              rw [h1v, h2v] at hv1
              exact add_left_cancel (hv1.trans hv2.symm)
            exact Prod.ext h1 (Prod.ext h2 h3)
          · intro p hp
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
            refine ⟨(p.1, p.2, p.1 + p.2), ?_, rfl⟩
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
            refine ⟨⟨hp.1.1.1, hp.1.1.2, Finset.mem_filter.mpr ⟨mem_univ _, hp.2⟩⟩, ?_, hp.1.2⟩
            apply Subtype.ext; simp only [Submodule.coe_add, Submodule.coe_zero]
            exact f2_add_self (p.1.val + p.2.val)
        simp_rw [h1, Finset.card_filter]
        rw [Finset.sum_comm]
        simp
      exact_mod_cast hnat
    rw [hsumP]
    dsimp only [dBC]; unfold edgeDens
    simp only [hBi_ne, hCj_ne, or_self, if_false]
    ring
  have hmarg_xz : ∀ a c : B.W, ∑ b : B.W, f' a b c = w * dBD (B.labB q a) (B.labD q c) := by
    intro a c
    set i := B.labB q a
    set k := B.labD q c
    have ha : a ∈ Bset B q i := Finset.mem_filter.mpr ⟨mem_univ a, rfl⟩
    have hc_mem : c ∈ Dset B q k := Finset.mem_filter.mpr ⟨mem_univ c, rfl⟩
    have hBi_ne : (Bset B q i).card ≠ 0 := (Finset.card_pos.mpr ⟨a, ha⟩).ne'
    have hDk_ne : (Dset B q k).card ≠ 0 := (Finset.card_pos.mpr ⟨c, hc_mem⟩).ne'
    have hBi_r : ((Bset B q i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hBi_ne
    have hDk_r : ((Dset B q k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hDk_ne
    have hsum_b : ∑ b : B.W, f' a b c = ∑ j : Fin B.m, ((Cset B q j).card : ℝ) * val' i j k := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := B.labC q)
        (f := fun b => f' a b c) (fun _ _ => mem_univ _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      change ∑ b ∈ Cset B q j, f' a b c = ((Cset B q j).card : ℝ) * val' i j k
      have hb : ∀ b ∈ Cset B q j, f' a b c = val' i j k := fun b hb => by
        dsimp only [f']; rw [(Finset.mem_filter.mp hb).2]
      rw [Finset.sum_congr rfl hb, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_b]
    have hterm : ∀ j : Fin B.m, ((Cset B q j).card : ℝ) * val' i j k =
        (Pcnt i j k : ℝ) * w / (((Bset B q i).card : ℝ) * ((Dset B q k).card : ℝ)) := by
      intro j
      have hm := hval'_mul i j k
      rw [eq_div_iff (mul_ne_zero hBi_r hDk_r)]
      linarith
    simp_rw [hterm, ← Finset.sum_div, ← Finset.sum_mul]
    have hsumP : ∑ j : Fin B.m, (Pcnt i j k : ℝ) =
        (((Bset B q i ×ˢ Dset B q k).filter (fun p => eBD A B.W q p.1 p.2)).card : ℝ) := by
      have hnat : ∑ j : Fin B.m, Pcnt i j k =
          ((Bset B q i ×ˢ Dset B q k).filter (fun p => eBD A B.W q p.1 p.2)).card := by
        have h1 : ∀ j : Fin B.m, Pcnt i j k =
            (((Bset B q i ×ˢ Dset B q k).filter (fun p => eBD A B.W q p.1 p.2)).filter
              (fun p => B.labC q (p.1 + p.2) = j)).card := by
          intro j
          refine Finset.card_bij (fun t _ => (t.1, t.2.2)) ?_ ?_ ?_
          · intro t ht
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
            rcases ht with ⟨⟨hB, hC, hD⟩, hsum0, hA⟩
            have hb_eq : t.1 + t.2.2 = t.2.1 := by
              apply Subtype.ext
              have hv : t.1.val + t.2.1.val + t.2.2.val = 0 := congrArg Subtype.val hsum0
              calc t.1.val + t.2.2.val
                  = (t.1.val + t.2.1.val + t.2.2.val) + t.2.1.val := by
                    calc t.1.val + t.2.2.val
                        = t.1.val + (t.2.1.val + t.2.1.val) + t.2.2.val := by rw [f2_add_self, add_zero]
                      _ = (t.1.val + t.2.1.val + t.2.2.val) + t.2.1.val := by abel
                _ = t.2.1.val := by rw [hv, zero_add]
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨⟨hB, hD⟩, by change (t.1, t.1 + t.2.2) ∈ A_box A B.W q; rw [hb_eq]; exact hA⟩,
              by rw [hb_eq]; exact (Finset.mem_filter.mp hC).2⟩
          · intro t₁ ht₁ t₂ ht₂ heq
            have h1 := congrArg Prod.fst heq
            have h3 := congrArg Prod.snd heq
            simp only [mem_filter] at ht₁ ht₂
            have h2 : t₁.2.1 = t₂.2.1 := by
              apply Subtype.ext
              have hv1 : t₁.1.val + t₁.2.1.val + t₁.2.2.val = 0 := congrArg Subtype.val ht₁.2.1
              have hv2 : t₂.1.val + t₂.2.1.val + t₂.2.2.val = 0 := congrArg Subtype.val ht₂.2.1
              have h1v : t₁.1.val = t₂.1.val := congrArg Subtype.val h1
              have h3v : t₁.2.2.val = t₂.2.2.val := congrArg Subtype.val h3
              rw [h1v, h3v] at hv1
              exact add_left_cancel (add_right_cancel (hv1.trans hv2.symm))
            exact Prod.ext h1 (Prod.ext h2 h3)
          · intro p hp
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
            refine ⟨(p.1, p.1 + p.2, p.2), ?_, rfl⟩
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
            refine ⟨⟨hp.1.1.1, Finset.mem_filter.mpr ⟨mem_univ _, hp.2⟩, hp.1.1.2⟩, ?_, hp.1.2⟩
            apply Subtype.ext; simp only [Submodule.coe_add, Submodule.coe_zero]
            calc p.1.val + (p.1.val + p.2.val) + p.2.val
                = (p.1.val + p.1.val) + (p.2.val + p.2.val) := by abel
              _ = 0 := by simp only [f2_add_self, zero_add]
        simp_rw [h1, Finset.card_filter]
        rw [Finset.sum_comm]
        simp
      exact_mod_cast hnat
    rw [hsumP]
    dsimp only [dBD]; unfold edgeDens
    simp only [hBi_ne, hDk_ne, or_self, if_false]
    ring
  have hmarg_yz : ∀ b c : B.W, ∑ a : B.W, f' a b c = w * dCD (B.labC q b) (B.labD q c) := by
    intro b c
    set j := B.labC q b
    set k := B.labD q c
    have hb_mem : b ∈ Cset B q j := Finset.mem_filter.mpr ⟨mem_univ b, rfl⟩
    have hc_mem : c ∈ Dset B q k := Finset.mem_filter.mpr ⟨mem_univ c, rfl⟩
    have hCj_ne : (Cset B q j).card ≠ 0 := (Finset.card_pos.mpr ⟨b, hb_mem⟩).ne'
    have hDk_ne : (Dset B q k).card ≠ 0 := (Finset.card_pos.mpr ⟨c, hc_mem⟩).ne'
    have hCj_r : ((Cset B q j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hCj_ne
    have hDk_r : ((Dset B q k).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hDk_ne
    have hsum_a : ∑ a : B.W, f' a b c = ∑ i : Fin B.m, ((Bset B q i).card : ℝ) * val' i j k := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := B.labB q)
        (f := fun a => f' a b c) (fun _ _ => mem_univ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ∑ a ∈ Bset B q i, f' a b c = ((Bset B q i).card : ℝ) * val' i j k
      have ha : ∀ a ∈ Bset B q i, f' a b c = val' i j k := fun a ha => by
        dsimp only [f']; rw [(Finset.mem_filter.mp ha).2]
      rw [Finset.sum_congr rfl ha, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_a]
    have hterm : ∀ i : Fin B.m, ((Bset B q i).card : ℝ) * val' i j k =
        (Pcnt i j k : ℝ) * w / (((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ)) := by
      intro i
      have hm := hval'_mul i j k
      rw [eq_div_iff (mul_ne_zero hCj_r hDk_r)]
      linarith
    simp_rw [hterm, ← Finset.sum_div, ← Finset.sum_mul]
    have hsumP : ∑ i : Fin B.m, (Pcnt i j k : ℝ) =
        (((Cset B q j ×ˢ Dset B q k).filter (fun p => eCD A B.W q p.1 p.2)).card : ℝ) := by
      have hnat : ∑ i : Fin B.m, Pcnt i j k =
          ((Cset B q j ×ˢ Dset B q k).filter (fun p => eCD A B.W q p.1 p.2)).card := by
        have h1 : ∀ i : Fin B.m, Pcnt i j k =
            (((Cset B q j ×ˢ Dset B q k).filter (fun p => eCD A B.W q p.1 p.2)).filter
              (fun p => B.labB q (p.1 + p.2) = i)).card := by
          intro i
          refine Finset.card_bij (fun t _ => (t.2.1, t.2.2)) ?_ ?_ ?_
          · intro t ht
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
            rcases ht with ⟨⟨hB, hC, hD⟩, hsum0, hA⟩
            have ha_eq : t.2.1 + t.2.2 = t.1 := by
              apply Subtype.ext
              have hv : t.1.val + t.2.1.val + t.2.2.val = 0 := congrArg Subtype.val hsum0
              calc t.2.1.val + t.2.2.val
                  = (t.1.val + t.2.1.val + t.2.2.val) + t.1.val := by
                    calc t.2.1.val + t.2.2.val
                        = (t.1.val + t.1.val) + t.2.1.val + t.2.2.val := by rw [f2_add_self, zero_add]
                      _ = (t.1.val + t.2.1.val + t.2.2.val) + t.1.val := by abel
                _ = t.1.val := by rw [hv, zero_add]
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨⟨hC, hD⟩, by change (t.2.1 + t.2.2, t.2.1) ∈ A_box A B.W q; rw [ha_eq]; exact hA⟩,
              by rw [ha_eq]; exact (Finset.mem_filter.mp hB).2⟩
          · intro t₁ ht₁ t₂ ht₂ heq
            have h2 := congrArg Prod.fst heq
            have h3 := congrArg Prod.snd heq
            simp only [mem_filter] at ht₁ ht₂
            have h1 : t₁.1 = t₂.1 := by
              apply Subtype.ext
              have hv1 : t₁.1.val + t₁.2.1.val + t₁.2.2.val = 0 := congrArg Subtype.val ht₁.2.1
              have hv2 : t₂.1.val + t₂.2.1.val + t₂.2.2.val = 0 := congrArg Subtype.val ht₂.2.1
              have h2v : t₁.2.1.val = t₂.2.1.val := congrArg Subtype.val h2
              have h3v : t₁.2.2.val = t₂.2.2.val := congrArg Subtype.val h3
              rw [h2v, h3v] at hv1
              exact add_right_cancel (add_right_cancel (hv1.trans hv2.symm))
            exact Prod.ext h1 (Prod.ext h2 h3)
          · intro p hp
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
            refine ⟨(p.1 + p.2, p.1, p.2), ?_, rfl⟩
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
            refine ⟨⟨Finset.mem_filter.mpr ⟨mem_univ _, hp.2⟩, hp.1.1.1, hp.1.1.2⟩, ?_, hp.1.2⟩
            apply Subtype.ext; simp only [Submodule.coe_add, Submodule.coe_zero]
            calc p.1.val + p.2.val + p.1.val + p.2.val
                = (p.1.val + p.1.val) + (p.2.val + p.2.val) := by abel
              _ = 0 := by simp only [f2_add_self, zero_add]
        simp_rw [h1, Finset.card_filter]
        rw [Finset.sum_comm]
        simp
      exact_mod_cast hnat
    rw [hsumP]
    dsimp only [dCD]; unfold edgeDens
    simp only [hCj_ne, hDk_ne, or_self, if_false]
    ring
  -- Step 3: Average of f' equals alphaBox, and ∑ (f' - f) ≤ ε * w^3 by Fourier bound.
  have hsum_f' : ∑ a : B.W, ∑ b : B.W, ∑ c : B.W, f' a b c = alphaBox A B.W q * w ^ 3 := by
    rw [hsum_by_lab val']
    simp_rw [hval'_mul, ← Finset.sum_mul]
    have hPtot : ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, (Pcnt i j k : ℝ) =
        ((A_box A B.W q).card : ℝ) := by
      have hnat : ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, Pcnt i j k = (A_box A B.W q).card := by
        have h1 : ∀ i j k : Fin B.m, Pcnt i j k =
            ((A_box A B.W q).filter
              (fun p => B.labB q p.1 = i ∧ B.labC q p.2 = j ∧ B.labD q (p.1 + p.2) = k)).card := by
          intro i j k
          refine Finset.card_bij (fun t _ => (t.1, t.2.1)) ?_ ?_ ?_
          · intro t ht
            simp only [mem_filter, mem_product, Bset, Cset, Dset, mem_univ, true_and] at ht ⊢
            rcases ht with ⟨⟨hB, hC, hD⟩, hsum0, hA⟩
            have hc_eq : t.1 + t.2.1 = t.2.2 := by
              apply Subtype.ext
              have hv : t.1.val + t.2.1.val + t.2.2.val = 0 := congrArg Subtype.val hsum0
              calc t.1.val + t.2.1.val
                  = (t.1.val + t.2.1.val + t.2.2.val) + t.2.2.val := by rw [add_assoc, f2_add_self, add_zero]
                _ = t.2.2.val := by rw [hv, zero_add]
            exact ⟨hA, hB, hC, by rw [hc_eq]; exact hD⟩
          · intro t₁ ht₁ t₂ ht₂ heq
            have h1 := congrArg Prod.fst heq
            have h2 := congrArg Prod.snd heq
            simp only [mem_filter] at ht₁ ht₂
            have h3 : t₁.2.2 = t₂.2.2 := by
              apply Subtype.ext
              have hv1 : t₁.1.val + t₁.2.1.val + t₁.2.2.val = 0 := congrArg Subtype.val ht₁.2.1
              have hv2 : t₂.1.val + t₂.2.1.val + t₂.2.2.val = 0 := congrArg Subtype.val ht₂.2.1
              have h1v : t₁.1.val = t₂.1.val := congrArg Subtype.val h1
              have h2v : t₁.2.1.val = t₂.2.1.val := congrArg Subtype.val h2
              rw [h1v, h2v] at hv1
              exact add_left_cancel (hv1.trans hv2.symm)
            exact Prod.ext h1 (Prod.ext h2 h3)
          · intro p hp
            simp only [mem_filter] at hp
            refine ⟨(p.1, p.2, p.1 + p.2), ?_, rfl⟩
            simp only [mem_filter, mem_product, Bset, Cset, Dset, mem_univ, true_and]
            refine ⟨⟨hp.2.1, hp.2.2.1, hp.2.2.2⟩, ?_, hp.1⟩
            apply Subtype.ext; simp only [Submodule.coe_add, Submodule.coe_zero]
            exact f2_add_self (p.1.val + p.2.val)
        simp_rw [h1, Finset.card_filter]
        symm
        calc (A_box A B.W q).card = ∑ _p ∈ A_box A B.W q, (1 : ℕ) := by simp
          _ = ∑ p ∈ A_box A B.W q, ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
                if B.labB q p.1 = i ∧ B.labC q p.2 = j ∧ B.labD q (p.1 + p.2) = k then 1 else 0 := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_eq_single (B.labB q p.1)]
              · rw [Finset.sum_eq_single (B.labC q p.2)]
                · rw [Finset.sum_eq_single (B.labD q (p.1 + p.2))]
                  · simp
                  · intro k _ hk; simp [hk.symm]
                  · intro h; exact absurd (mem_univ _) h
                · intro j _ hj; refine Finset.sum_eq_zero fun k _ => ?_; simp [hj.symm]
                · intro h; exact absurd (mem_univ _) h
              · intro i _ hi
                refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
                simp [hi.symm]
              · intro h; exact absurd (mem_univ _) h
          _ = ∑ i : Fin B.m, ∑ p ∈ A_box A B.W q, ∑ j : Fin B.m, ∑ k : Fin B.m,
                if B.labB q p.1 = i ∧ B.labC q p.2 = j ∧ B.labD q (p.1 + p.2) = k then 1 else 0 := by
              rw [Finset.sum_comm]
          _ = ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ p ∈ A_box A B.W q, ∑ k : Fin B.m,
                if B.labB q p.1 = i ∧ B.labC q p.2 = j ∧ B.labD q (p.1 + p.2) = k then 1 else 0 := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, ∑ p ∈ A_box A B.W q,
                if B.labB q p.1 = i ∧ B.labC q p.2 = j ∧ B.labD q (p.1 + p.2) = k then 1 else 0 := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      exact_mod_cast hnat
    rw [hPtot]
    unfold alphaBox
    dsimp only [w]
    field_simp [hw_pos.ne']
  have hdiff_le : ∑ a : B.W, ∑ b : B.W, ∑ c : B.W, (f' a b c - f a b c) ≤ ε * w ^ 3 := by
    have heq : ∑ a : B.W, ∑ b : B.W, ∑ c : B.W, (f' a b c - f a b c) =
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) *
            (val' i j k - min (val' i j k) 1) :=
      hsum_by_lab (fun i j k => val' i j k - min (val' i j k) 1)
    rw [heq]
    have hterm : ∀ i j k : Fin B.m,
        ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) *
          (val' i j k - min (val' i j k) 1) ≤ (ε / (B.m : ℝ) ^ 3) * w ^ 3 := by
      intro i j k
      have hP_le_zero : (Pcnt i j k : ℝ) ≤
          (((Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter (fun t => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) := by
        have hsub : (Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter
            (fun t => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A_box A B.W q) ⊆
            (Bset B q i ×ˢ Cset B q j ×ˢ Dset B q k).filter (fun t => t.1 + t.2.1 + t.2.2 = 0) := by
          intro t ht
          rw [Finset.mem_filter] at ht ⊢
          exact ⟨ht.1, ht.2.1⟩
        exact_mod_cast Finset.card_le_card hsub
      have hfour := triple_zero_sum_le B.W (Bset B q i) (Cset B q j) (Dset B q k)
        (η := ε / (B.m : ℝ) ^ 3) (by positivity)
        (fun r hr => (hUnif i r hr).1)
      have hP_bound : (Pcnt i j k : ℝ) * w ≤
          ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) +
          (ε / (B.m : ℝ) ^ 3) * w ^ 3 := by
        have h1 : (Pcnt i j k : ℝ) / w ^ 2 ≤
            (((Bset B q i).card : ℝ) / w) * (((Cset B q j).card : ℝ) / w) * (((Dset B q k).card : ℝ) / w) +
            ε / (B.m : ℝ) ^ 3 :=
          (div_le_div_of_nonneg_right hP_le_zero (sq_nonneg w)).trans hfour
        have h2 := mul_le_mul_of_nonneg_right h1 hw3_pos.le
        have hL : (Pcnt i j k : ℝ) / w ^ 2 * w ^ 3 = (Pcnt i j k : ℝ) * w := by
          field_simp [hw_pos.ne']
        have hR : ((((Bset B q i).card : ℝ) / w) * (((Cset B q j).card : ℝ) / w) *
            (((Dset B q k).card : ℝ) / w) + ε / (B.m : ℝ) ^ 3) * w ^ 3 =
            ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) +
            (ε / (B.m : ℝ) ^ 3) * w ^ 3 := by
          field_simp [hw_pos.ne']
        linarith
      by_cases hv : val' i j k ≤ 1
      · rw [min_eq_left hv, sub_self, mul_zero]; positivity
      · push Not at hv
        rw [min_eq_right hv.le]
        have hm := hval'_mul i j k
        linarith
    calc ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          ((Bset B q i).card : ℝ) * ((Cset B q j).card : ℝ) * ((Dset B q k).card : ℝ) *
            (val' i j k - min (val' i j k) 1)
        ≤ ∑ _i : Fin B.m, ∑ _j : Fin B.m, ∑ _k : Fin B.m, ((ε / (B.m : ℝ) ^ 3) * w ^ 3) :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => hterm i j k
      _ = ε * w ^ 3 := by
          have hm_ne : (B.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr B.hm.ne'
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hm_ne]
  -- Step 4: Apply weighted_triforce_bound to f and compare T(f) ≤ T(f') = Tmain / w^3.
  have hμf_ge : max 0 (alphaBox A B.W q - ε) ≤
      (∑ a : B.W, ∑ b : B.W, ∑ c : B.W, f a b c) / w ^ 3 := by
    apply max_le
    · exact div_nonneg (sum_nonneg fun a _ => sum_nonneg fun b _ => sum_nonneg fun c _ => hf0 a b c)
        hw3_pos.le
    · rw [le_div_iff₀ hw3_pos]
      have hsub : (∑ a : B.W, ∑ b : B.W, ∑ c : B.W, f' a b c) -
          (∑ a : B.W, ∑ b : B.W, ∑ c : B.W, f a b c) =
          ∑ a : B.W, ∑ b : B.W, ∑ c : B.W, (f' a b c - f a b c) := by
        simp only [Finset.sum_sub_distrib]
      linarith
  have htrif_f := weighted_triforce_bound hc hb hH f hf0 hf1
  dsimp only at htrif_f
  have hpow_le : b * (max 0 (alphaBox A B.W q - ε)) ^ c ≤
      b * ((∑ a : B.W, ∑ b : B.W, ∑ c : B.W, f a b c) / w ^ 3) ^ c :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_left _ _) hμf_ge (by linarith)) hb.le
  have hTf_le_Tf' :
      (∑ a : B.W, ∑ b : B.W, ∑ c : B.W,
        (∑ c' : B.W, f a b c') * (∑ b' : B.W, f a b' c) * (∑ a' : B.W, f a' b c)) / w ^ 6 ≤
      Tmain / w ^ 3 := by
    have hnum : ∑ a : B.W, ∑ b : B.W, ∑ c : B.W,
        (∑ c' : B.W, f a b c') * (∑ b' : B.W, f a b' c) * (∑ a' : B.W, f a' b c) ≤
        w ^ 3 * Tmain := by
      have h1 : ∑ a : B.W, ∑ b : B.W, ∑ c : B.W,
          (∑ c' : B.W, f a b c') * (∑ b' : B.W, f a b' c) * (∑ a' : B.W, f a' b c) ≤
          ∑ a : B.W, ∑ b : B.W, ∑ c : B.W,
            (∑ c' : B.W, f' a b c') * (∑ b' : B.W, f' a b' c) * (∑ a' : B.W, f' a' b c) := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => ?_
        have h10 : 0 ≤ ∑ c' : B.W, f a b c' := sum_nonneg fun c' _ => hf0 a b c'
        have h20 : 0 ≤ ∑ b' : B.W, f a b' c := sum_nonneg fun b' _ => hf0 a b' c
        have h30 : 0 ≤ ∑ a' : B.W, f a' b c := sum_nonneg fun a' _ => hf0 a' b c
        have h1' : ∑ c' : B.W, f a b c' ≤ ∑ c' : B.W, f' a b c' :=
          sum_le_sum fun c' _ => hf_le_f' a b c'
        have h2' : ∑ b' : B.W, f a b' c ≤ ∑ b' : B.W, f' a b' c :=
          sum_le_sum fun b' _ => hf_le_f' a b' c
        have h3' : ∑ a' : B.W, f a' b c ≤ ∑ a' : B.W, f' a' b c :=
          sum_le_sum fun a' _ => hf_le_f' a' b c
        exact mul_le_mul (mul_le_mul h1' h2' h20 (h10.trans h1')) h3' h30
          (mul_nonneg (h10.trans h1') (h20.trans h2'))
      have h2 : ∑ a : B.W, ∑ b : B.W, ∑ c : B.W,
          (∑ c' : B.W, f' a b c') * (∑ b' : B.W, f' a b' c) * (∑ a' : B.W, f' a' b c) =
          w ^ 3 * Tmain := by
        simp_rw [hmarg_xy, hmarg_xz, hmarg_yz]
        have h3 := hsum_by_lab (fun i j k => (w * dBC i j) * (w * dBD i k) * (w * dCD j k))
        rw [h3]
        dsimp only [Tmain]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      linarith
    have hdiv : (∑ a : B.W, ∑ b : B.W, ∑ c : B.W,
        (∑ c' : B.W, f a b c') * (∑ b' : B.W, f a b' c) * (∑ a' : B.W, f a' b c)) / w ^ 6 ≤
        (w ^ 3 * Tmain) / w ^ 6 :=
      div_le_div_of_nonneg_right hnum (pow_nonneg hw_pos.le 6)
    have hsimp : (w ^ 3 * Tmain) / w ^ 6 = Tmain / w ^ 3 := by field_simp [hw_pos.ne']
    linarith
  have hTmain_ge : b * (max 0 (alphaBox A B.W q - ε)) ^ c * w ^ 3 ≤ Tmain := by
    have hle : b * (max 0 (alphaBox A B.W q - ε)) ^ c ≤ Tmain / w ^ 3 :=
      hpow_le.trans (htrif_f.trans hTf_le_Tf')
    rwa [le_div_iff₀ hw3_pos] at hle
  exact hTmain_ge

/-- Lower bound on the number of corners in a single regular outer box (Mandache Claim `1box`). -/
private lemma regular_box_corners_ge
    {c b ε : ℝ} (hc : 1 ≤ c) (hb : 0 < b) (hε : 0 < ε)
    (hH : ∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
      let xy (e : Fin q × Fin q × Fin q) := (e.1, e.2.1)
      let xz (e : Fin q × Fin q × Fin q) := (e.1, e.2.2)
      let yz (e : Fin q × Fin q × Fin q) := (e.2.1, e.2.2)
      let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
        (H.filter (fun e => proj e = x)).card
      let density : ℝ := H.card / (q : ℝ) ^ 3
      let triforce := (∑ e : Fin q × Fin q × Fin q,
        deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q : ℝ) ^ 6
      b * density ^ c ≤ triforce)
    {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n)) (B : Boxing n) (q : Q B.W)
    (hUnif : BoxUnif ε B q) (hQR : BoxQR ε A B q) :
    (b * (max 0 (alphaBox A B.W q - ε)) ^ c - 8 * ε) * (Fintype.card B.W : ℝ) ^ 3 ≤
    (cornersBox A B.W q : ℝ) := by
  have h1 := cornersBox_ge_triforce_sum hε A B q hQR
  have h2 := triforce_sum_ge_weighted hc hb hε hH A B q hUnif
  linarith

end BoxCounting

/- ## Section 6: Jensen Averaging, Bijection, and Pigeonhole -/

section FinalAssembly

/-- Convexity of `t ↦ (max 0 (t - ε)) ^ c` on `ℝ` for `c ≥ 1`. -/
private lemma convexOn_posPart_rpow {c : ℝ} (hc : 1 ≤ c) (ε : ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => (max 0 (t - ε)) ^ c) := by
  have hrpow : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ c) := convexOn_rpow hc
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hx0 : 0 ≤ max 0 (x - ε) := le_max_left _ _
  have hy0 : 0 ≤ max 0 (y - ε) := le_max_left _ _
  have hlin : max 0 ((a • x + b • y) - ε) ≤ a * max 0 (x - ε) + b * max 0 (y - ε) := by
    simp only [smul_eq_mul]
    apply max_le
    · exact add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
    · have h1 : x - ε ≤ max 0 (x - ε) := le_max_right _ _
      have h2 : y - ε ≤ max 0 (y - ε) := le_max_right _ _
      have h3 : a * x + b * y - ε = a * (x - ε) + b * (y - ε) := by
        calc a * x + b * y - ε = a * x + b * y - (a + b) * ε := by rw [hab, one_mul]
          _ = a * (x - ε) + b * (y - ε) := by ring
      rw [h3]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  have hstep1 : (max 0 ((a • x + b • y) - ε)) ^ c ≤ (a * max 0 (x - ε) + b * max 0 (y - ε)) ^ c :=
    Real.rpow_le_rpow (le_max_left _ _) hlin (by linarith)
  have hstep2 := hrpow.2 hx0 hy0 ha hb hab
  simp only [smul_eq_mul] at hstep2 ⊢
  exact hstep1.trans hstep2

/-- Partitioning `A` across outer boxes preserves total cardinality. -/
private lemma sum_card_A_box {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) :
    ∑ q : Q W, (A_box A W q).card = A.card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun x _ => (rep W x.1.1 + x.2.1.val, rep W x.1.2 + x.2.2.val)) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.2).2
  · intro x₁ _ x₂ _ heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have hq1 : x₁.1.1 = x₂.1.1 := by
      have hm := congrArg (Submodule.Quotient.mk (p := W)) h1
      change Submodule.Quotient.mk (p := W) (rep W x₁.1.1) + Submodule.Quotient.mk (p := W) x₁.2.1.val =
        Submodule.Quotient.mk (p := W) (rep W x₂.1.1) + Submodule.Quotient.mk (p := W) x₂.2.1.val at hm
      rw [mk_rep, mk_rep, (Submodule.Quotient.mk_eq_zero W).mpr x₁.2.1.prop,
        (Submodule.Quotient.mk_eq_zero W).mpr x₂.2.1.prop, add_zero, add_zero] at hm
      exact hm
    have hq2 : x₁.1.2 = x₂.1.2 := by
      have hm := congrArg (Submodule.Quotient.mk (p := W)) h2
      change Submodule.Quotient.mk (p := W) (rep W x₁.1.2) + Submodule.Quotient.mk (p := W) x₁.2.2.val =
        Submodule.Quotient.mk (p := W) (rep W x₂.1.2) + Submodule.Quotient.mk (p := W) x₂.2.2.val at hm
      rw [mk_rep, mk_rep, (Submodule.Quotient.mk_eq_zero W).mpr x₁.2.2.prop,
        (Submodule.Quotient.mk_eq_zero W).mpr x₂.2.2.prop, add_zero, add_zero] at hm
      exact hm
    rw [hq1] at h1; rw [hq2] at h2
    exact Sigma.ext (Prod.ext hq1 hq2)
      (heq_of_eq (Prod.ext (Subtype.ext (add_left_cancel h1)) (Subtype.ext (add_left_cancel h2))))
  · intro p hp
    let q₁ : 𝔽₂ n ⧸ W := Submodule.Quotient.mk (p := W) p.1
    let q₂ : 𝔽₂ n ⧸ W := Submodule.Quotient.mk (p := W) p.2
    let a : W := ⟨p.1 + rep W q₁, add_rep_mem W p.1⟩
    let b : W := ⟨p.2 + rep W q₂, add_rep_mem W p.2⟩
    have ha : rep W q₁ + a.val = p.1 := by
      dsimp only [a]
      calc rep W q₁ + (p.1 + rep W q₁) = (rep W q₁ + rep W q₁) + p.1 := by abel
        _ = p.1 := by simp only [f2_add_self, zero_add]
    have hb : rep W q₂ + b.val = p.2 := by
      dsimp only [b]
      calc rep W q₂ + (p.2 + rep W q₂) = (rep W q₂ + rep W q₂) + p.2 := by abel
        _ = p.2 := by simp only [f2_add_self, zero_add]
    refine ⟨⟨(q₁, q₂), (a, b)⟩, ?_, Prod.ext ha hb⟩
    rw [Finset.mem_sigma]
    refine ⟨mem_univ _, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [ha, hb]; exact hp

/-- Exact bijection between outer-box corners and corners with common difference `d ∈ W`. -/
private lemma sum_cornersBox_eq_sum_S {n : ℕ} (A : Finset (𝔽₂ n × 𝔽₂ n))
    (W : Submodule (ZMod 2) (𝔽₂ n)) :
    ∑ q : Q W, cornersBox A W q = ∑ d : W, (Green19.S d.val A).card := by
  unfold cornersBox
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  refine Finset.card_bij
    (fun x _ => ⟨x.2.1 + x.2.2.1 + x.2.2.2,
      (rep W x.1.1 + x.2.1.val, rep W x.1.2 + x.2.2.1.val)⟩) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_sigma] at hx ⊢
    refine ⟨mem_univ _, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have hx' := (Finset.mem_filter.mp hx.2).2
    rcases hx' with ⟨h1, h2, h3⟩
    have h1' : (rep W x.1.1 + x.2.1.val, rep W x.1.2 + x.2.2.1.val) ∈ A :=
      (Finset.mem_filter.mp h1).2
    have h2' : (rep W x.1.1 + x.2.1.val, rep W x.1.2 + (x.2.1 + x.2.2.2).val) ∈ A :=
      (Finset.mem_filter.mp h2).2
    have h3' : (rep W x.1.1 + (x.2.2.1 + x.2.2.2).val, rep W x.1.2 + x.2.2.1.val) ∈ A :=
      (Finset.mem_filter.mp h3).2
    refine ⟨h1', ?_, ?_⟩
    · have hx_eq : rep W x.1.1 + x.2.1.val + (x.2.1 + x.2.2.1 + x.2.2.2).val =
          rep W x.1.1 + (x.2.2.1 + x.2.2.2).val := by
        simp only [Submodule.coe_add]
        calc rep W x.1.1 + x.2.1.val + (x.2.1.val + x.2.2.1.val + x.2.2.2.val)
            = rep W x.1.1 + (x.2.1.val + x.2.1.val) + (x.2.2.1.val + x.2.2.2.val) := by abel
          _ = rep W x.1.1 + (x.2.2.1.val + x.2.2.2.val) := by rw [f2_add_self, add_zero]
      rw [hx_eq]; exact h3'
    · have hy_eq : rep W x.1.2 + x.2.2.1.val + (x.2.1 + x.2.2.1 + x.2.2.2).val =
          rep W x.1.2 + (x.2.1 + x.2.2.2).val := by
        simp only [Submodule.coe_add]
        calc rep W x.1.2 + x.2.2.1.val + (x.2.1.val + x.2.2.1.val + x.2.2.2.val)
            = rep W x.1.2 + (x.2.2.1.val + x.2.2.1.val) + (x.2.1.val + x.2.2.2.val) := by abel
          _ = rep W x.1.2 + (x.2.1.val + x.2.2.2.val) := by rw [f2_add_self, add_zero]
      rw [hy_eq]; exact h2'
  · intro x₁ _ x₂ _ heq
    have hd : x₁.2.1 + x₁.2.2.1 + x₁.2.2.2 = x₂.2.1 + x₂.2.2.1 + x₂.2.2.2 :=
      congrArg Sigma.fst heq
    have hp : (rep W x₁.1.1 + x₁.2.1.val, rep W x₁.1.2 + x₁.2.2.1.val) =
        (rep W x₂.1.1 + x₂.2.1.val, rep W x₂.1.2 + x₂.2.2.1.val) :=
      eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    have hu := congrArg Prod.fst hp
    have hv := congrArg Prod.snd hp
    have hq1 : x₁.1.1 = x₂.1.1 := by
      have hm := congrArg (Submodule.Quotient.mk (p := W)) hu
      change Submodule.Quotient.mk (p := W) (rep W x₁.1.1) + Submodule.Quotient.mk (p := W) x₁.2.1.val =
        Submodule.Quotient.mk (p := W) (rep W x₂.1.1) + Submodule.Quotient.mk (p := W) x₂.2.1.val at hm
      rw [mk_rep, mk_rep, (Submodule.Quotient.mk_eq_zero W).mpr x₁.2.1.prop,
        (Submodule.Quotient.mk_eq_zero W).mpr x₂.2.1.prop, add_zero, add_zero] at hm
      exact hm
    have hq2 : x₁.1.2 = x₂.1.2 := by
      have hm := congrArg (Submodule.Quotient.mk (p := W)) hv
      change Submodule.Quotient.mk (p := W) (rep W x₁.1.2) + Submodule.Quotient.mk (p := W) x₁.2.2.1.val =
        Submodule.Quotient.mk (p := W) (rep W x₂.1.2) + Submodule.Quotient.mk (p := W) x₂.2.2.1.val at hm
      rw [mk_rep, mk_rep, (Submodule.Quotient.mk_eq_zero W).mpr x₁.2.2.1.prop,
        (Submodule.Quotient.mk_eq_zero W).mpr x₂.2.2.1.prop, add_zero, add_zero] at hm
      exact hm
    rw [hq1] at hu; rw [hq2] at hv
    have ha : x₁.2.1 = x₂.2.1 := Subtype.ext (add_left_cancel hu)
    have hb : x₁.2.2.1 = x₂.2.2.1 := Subtype.ext (add_left_cancel hv)
    rw [ha, hb] at hd
    have hc : x₁.2.2.2 = x₂.2.2.2 := add_left_cancel hd
    exact Sigma.ext (Prod.ext hq1 hq2) (heq_of_eq (Prod.ext ha (Prod.ext hb hc)))
  · intro y hy
    rw [Finset.mem_sigma] at hy
    have hy' : Green19.IsCorner A y.2.1 y.2.2 y.1.val := (Finset.mem_filter.mp hy.2).2
    let q₁ : 𝔽₂ n ⧸ W := Submodule.Quotient.mk (p := W) y.2.1
    let q₂ : 𝔽₂ n ⧸ W := Submodule.Quotient.mk (p := W) y.2.2
    let a : W := ⟨y.2.1 + rep W q₁, add_rep_mem W y.2.1⟩
    let b : W := ⟨y.2.2 + rep W q₂, add_rep_mem W y.2.2⟩
    let c : W := a + b + y.1
    have ha : rep W q₁ + a.val = y.2.1 := by
      dsimp only [a]
      calc rep W q₁ + (y.2.1 + rep W q₁) = (rep W q₁ + rep W q₁) + y.2.1 := by abel
        _ = y.2.1 := by simp only [f2_add_self, zero_add]
    have hb : rep W q₂ + b.val = y.2.2 := by
      dsimp only [b]
      calc rep W q₂ + (y.2.2 + rep W q₂) = (rep W q₂ + rep W q₂) + y.2.2 := by abel
        _ = y.2.2 := by simp only [f2_add_self, zero_add]
    have hd : a + b + c = y.1 := by
      apply Subtype.ext; dsimp only [c]; simp only [Submodule.coe_add]
      calc a.val + b.val + (a.val + b.val + y.1.val)
          = (a.val + a.val) + (b.val + b.val) + y.1.val := by abel
        _ = y.1.val := by simp only [f2_add_self, zero_add]
    refine ⟨⟨(q₁, q₂), (a, b, c)⟩, ?_, Sigma.ext hd (heq_of_eq (Prod.ext ha hb))⟩
    rw [Finset.mem_sigma]
    refine ⟨mem_univ _, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have hbd : rep W q₂ + (a + c).val = y.2.2 + y.1.val := by
      dsimp only [c]; simp only [Submodule.coe_add]
      calc rep W q₂ + (a.val + (a.val + b.val + y.1.val))
          = (a.val + a.val) + (rep W q₂ + b.val) + y.1.val := by abel
        _ = y.2.2 + y.1.val := by rw [f2_add_self, zero_add, hb]
    have hcd : rep W q₁ + (b + c).val = y.2.1 + y.1.val := by
      dsimp only [c]; simp only [Submodule.coe_add]
      calc rep W q₁ + (b.val + (a.val + b.val + y.1.val))
          = (b.val + b.val) + (rep W q₁ + a.val) + y.1.val := by abel
        _ = y.2.1 + y.1.val := by rw [f2_add_self, zero_add, ha]
    refine ⟨Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩,
            Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩,
            Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    · rw [ha, hb]; exact hy'.1
    · rw [ha, hbd]; exact hy'.2.2
    · rw [hcd, hb]; exact hy'.2.1

end FinalAssembly

end Green19H1

theorem OMA.cornersLower : OMA.R_Green19_green_19_R1.H1 := by
  intro c hc b hb hH
  refine ⟨b / 2, by linarith, fun α hα0 hα1 => ?_⟩
  -- Step 1: Choose ε ∈ (0, α) so that b * (α - ε)^c - (2 * b + 8) * ε ≥ (3/4) * b * α^c.
  have hαc_pos : 0 < α ^ c := Real.rpow_pos_of_pos hα0 c
  have hcont : ContinuousAt (fun t : ℝ => b * (α - t) ^ c - (2 * b + 8) * t) 0 := by
    have hsub : ContinuousAt (fun t : ℝ => α - t) 0 := continuousAt_const.sub continuousAt_id
    have hpow : ContinuousAt (fun t : ℝ => (α - t) ^ c) 0 :=
      ContinuousAt.rpow_const hsub (Or.inl (by simpa using hα0.ne'))
    exact (continuousAt_const.mul hpow).sub (continuousAt_const.mul continuousAt_id)
  have hval0 : (3 / 4 : ℝ) * b * α ^ c < b * (α - 0) ^ c - (2 * b + 8) * 0 := by
    simp only [sub_zero, mul_zero]; nlinarith
  have hnhds : ∀ᶠ t in 𝓝 (0 : ℝ), (3 / 4 : ℝ) * b * α ^ c < b * (α - t) ^ c - (2 * b + 8) * t :=
    hcont.eventually (Ioi_mem_nhds hval0)
  rw [Metric.eventually_nhds_iff] at hnhds
  rcases hnhds with ⟨δ, hδ_pos, hδ⟩
  set ε : ℝ := min (δ / 2) (α / 2)
  have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
  have hε_lt_α : ε < α := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hε_good : (3 / 4 : ℝ) * b * α ^ c ≤ b * (max 0 (α - ε)) ^ c - (2 * b + 8) * ε := by
    have hdist : dist ε 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hlt := hδ hdist
    rw [max_eq_right (by linarith : 0 ≤ α - ε)]
    exact hlt.le
  -- Step 2: Obtain uniform codimension bound d₀ from the Regularity Lemma.
  rcases Green19H1.regularity_lemma hε_pos with ⟨d₀, hd₀⟩
  -- Step 3: Choose kW ≥ 1 such that 1 / 2^kW ≤ (1/4) * b * α^c, and set n₀ := d₀ + kW.
  have hgap_pos : 0 < (1 / 4 : ℝ) * b * α ^ c := by positivity
  have hex_k : ∃ kW : ℕ, 1 ≤ kW ∧ (1 : ℝ) / (2 : ℝ) ^ kW ≤ (1 / 4 : ℝ) * b * α ^ c := by
    have htend : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ k)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hev := (htend.eventually (Iic_mem_nhds hgap_pos)).and (eventually_ge_atTop 1)
    rcases hev.exists with ⟨kW, hk1, hk2⟩
    refine ⟨kW, hk2, ?_⟩
    simpa [one_div, inv_pow] using hk1
  rcases hex_k with ⟨kW, hkW1, hkW⟩
  rw [Filter.eventually_atTop]
  refine ⟨d₀ + kW, fun n hn A hA => ?_⟩
  set N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
  have hN_pos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  rcases hd₀ n A with ⟨B, ⟨hCond1, hCond2⟩, hcod⟩
  set w : ℝ := (Fintype.card B.W : ℝ)
  have hw_pos : 0 < w := Nat.cast_pos.mpr Fintype.card_pos
  have hQ_pos : (0 : ℝ) < (Fintype.card (Green19H1.Q B.W) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  -- Lower bound w ≥ 2^kW ≥ 2.
  have hfinrank_ge : kW ≤ Module.finrank (ZMod 2) B.W := by
    have hsum := Green19H1.codim_add_finrank B.W
    omega
  have hw_ge_pow : (2 : ℝ) ^ kW ≤ w := by
    have hnat : 2 ^ kW ≤ Fintype.card B.W := by
      rw [Green19H1.card_subspace_eq_two_pow_finrank]
      exact Nat.pow_le_pow_right (by norm_num) hfinrank_ge
    dsimp only [w]; exact_mod_cast hnat
  have hw_ge_two : (2 : ℝ) ≤ w := by
    have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ kW := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hkW1
    linarith
  have hinv_w : 1 / w ≤ (1 / 4 : ℝ) * b * α ^ c :=
    (div_le_div_of_nonneg_left zero_le_one (by positivity) hw_ge_pow).trans hkW
  -- Key cardinality identity: |Q B.W| * w^2 = N^2.
  have hQw2 : (Fintype.card (Green19H1.Q B.W) : ℝ) * w ^ 2 = N ^ 2 := by
    have h1 : (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ) * w = N := by
      dsimp only [w, N]; exact_mod_cast Green19H1.card_quot_mul_card_subspace B.W
    have h2 : (Fintype.card (Green19H1.Q B.W) : ℝ) = (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ) ^ 2 := by
      simp [Green19H1.Q, sq]
    rw [h2, ← mul_pow, h1]
  -- Step 4: Jensen's inequality on g(t) = (max 0 (t - ε))^c over all outer boxes.
  let g : ℝ → ℝ := fun t => (max 0 (t - ε)) ^ c
  have havg_alpha : α ≤ (∑ q : Green19H1.Q B.W, Green19H1.alphaBox A B.W q) /
      (Fintype.card (Green19H1.Q B.W) : ℝ) := by
    have hsum : ∑ q : Green19H1.Q B.W, Green19H1.alphaBox A B.W q = (A.card : ℝ) / w ^ 2 := by
      unfold Green19H1.alphaBox
      rw [← Finset.sum_div]
      have hcard : ∑ q : Green19H1.Q B.W, ((Green19H1.A_box A B.W q).card : ℝ) = (A.card : ℝ) := by
        exact_mod_cast Green19H1.sum_card_A_box A B.W
      rw [hcard]
    rw [hsum, div_div, mul_comm, hQw2, le_div_iff₀ (pow_pos hN_pos 2)]
    exact hA
  have hg_mono : ∀ x y : ℝ, x ≤ y → g x ≤ g y := fun x y hxy =>
    Real.rpow_le_rpow (le_max_left _ _) (max_le_max_left 0 (by linarith)) (by linarith)
  have hjensen : (Fintype.card (Green19H1.Q B.W) : ℝ) * g α ≤
      ∑ q : Green19H1.Q B.W, g (Green19H1.alphaBox A B.W q) := by
    have hconv := Green19H1.convexOn_posPart_rpow hc ε
    have hmap := hconv.map_sum_le (t := (univ : Finset (Green19H1.Q B.W)))
      (w := fun _ => (1 : ℝ) / (Fintype.card (Green19H1.Q B.W) : ℝ))
      (p := fun q => Green19H1.alphaBox A B.W q)
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hQ_pos.ne'])
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul, ← Finset.mul_sum, one_div] at hmap
    have h1 : g α ≤ g ((Fintype.card (Green19H1.Q B.W) : ℝ)⁻¹ *
        ∑ q : Green19H1.Q B.W, Green19H1.alphaBox A B.W q) := by
      apply hg_mono
      simpa [div_eq_inv_mul] using havg_alpha
    have h2 : g α ≤ (Fintype.card (Green19H1.Q B.W) : ℝ)⁻¹ *
        ∑ q : Green19H1.Q B.W, g (Green19H1.alphaBox A B.W q) := h1.trans hmap
    have h3 := mul_le_mul_of_nonneg_left h2 hQ_pos.le
    rw [← mul_assoc, mul_inv_cancel₀ hQ_pos.ne', one_mul] at h3
    exact h3
  -- Step 5: Sum regular_box_corners_ge over regular outer boxes.
  let Reg : Finset (Green19H1.Q B.W) :=
    univ.filter (fun q => Green19H1.BoxUnif ε B q ∧ Green19H1.BoxQR ε A B q)
  let Irreg : Finset (Green19H1.Q B.W) := univ \ Reg
  have hIrreg_card : (Irreg.card : ℝ) ≤ 2 * ε * (Fintype.card (Green19H1.Q B.W) : ℝ) := by
    have hsub : Irreg ⊆ univ.filter (fun q : Green19H1.Q B.W => ¬ Green19H1.BoxUnif ε B q) ∪
        univ.filter (fun q : Green19H1.Q B.W => ¬ Green19H1.BoxQR ε A B q) := by
      intro q hq
      have hnot : q ∉ Reg := (Finset.mem_sdiff.mp hq).2
      have hnot_and : ¬ (Green19H1.BoxUnif ε B q ∧ Green19H1.BoxQR ε A B q) := fun h =>
        hnot (Finset.mem_filter.mpr ⟨mem_univ q, h⟩)
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h1 : Green19H1.BoxUnif ε B q
      · exact Or.inr ⟨mem_univ q, fun h2 => hnot_and ⟨h1, h2⟩⟩
      · exact Or.inl ⟨mem_univ q, h1⟩
    have hle1 : Irreg.card ≤ (univ.filter (fun q : Green19H1.Q B.W => ¬ Green19H1.BoxUnif ε B q)).card +
        (univ.filter (fun q : Green19H1.Q B.W => ¬ Green19H1.BoxQR ε A B q)).card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hle1r : (Irreg.card : ℝ) ≤
        ((univ.filter (fun q : Green19H1.Q B.W => ¬ Green19H1.BoxUnif ε B q)).card : ℝ) +
        ((univ.filter (fun q : Green19H1.Q B.W => ¬ Green19H1.BoxQR ε A B q)).card : ℝ) := by
      exact_mod_cast hle1
    unfold Green19H1.Cond1 at hCond1
    unfold Green19H1.Cond2 at hCond2
    linarith
  have hIrreg_g : ∑ q ∈ Irreg, g (Green19H1.alphaBox A B.W q) ≤
      2 * ε * (Fintype.card (Green19H1.Q B.W) : ℝ) := by
    calc ∑ q ∈ Irreg, g (Green19H1.alphaBox A B.W q)
        ≤ ∑ _q ∈ Irreg, (1 : ℝ) := by
          refine sum_le_sum fun q _ => ?_
          have h1 : Green19H1.alphaBox A B.W q ≤ 1 := Green19H1.alphaBox_le_one A B.W q
          have h2 : max 0 (Green19H1.alphaBox A B.W q - ε) ≤ 1 :=
            max_le zero_le_one (by linarith)
          calc g (Green19H1.alphaBox A B.W q)
              ≤ (1 : ℝ) ^ c := Real.rpow_le_rpow (le_max_left _ _) h2 (by linarith)
            _ = 1 := Real.one_rpow c
      _ = (Irreg.card : ℝ) := by simp
      _ ≤ 2 * ε * (Fintype.card (Green19H1.Q B.W) : ℝ) := hIrreg_card
  have hReg_g : (Fintype.card (Green19H1.Q B.W) : ℝ) * (g α - 2 * ε) ≤
      ∑ q ∈ Reg, g (Green19H1.alphaBox A B.W q) := by
    have hsplit : (∑ q ∈ Reg, g (Green19H1.alphaBox A B.W q)) +
        (∑ q ∈ Irreg, g (Green19H1.alphaBox A B.W q)) =
        ∑ q : Green19H1.Q B.W, g (Green19H1.alphaBox A B.W q) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    linarith
  have hcorners_tot : (b * g α - (2 * b + 8) * ε) * N ^ 2 * w ≤
      ∑ q : Green19H1.Q B.W, (Green19H1.cornersBox A B.W q : ℝ) := by
    have hsum_reg : ∑ q ∈ Reg, (b * g (Green19H1.alphaBox A B.W q) - 8 * ε) * w ^ 3 ≤
        ∑ q ∈ Reg, (Green19H1.cornersBox A B.W q : ℝ) := by
      refine sum_le_sum fun q hq => ?_
      have hq' := (Finset.mem_filter.mp hq).2
      exact Green19H1.regular_box_corners_ge hc hb hε_pos hH A B q hq'.1 hq'.2
    have hreg_le_tot : ∑ q ∈ Reg, (Green19H1.cornersBox A B.W q : ℝ) ≤
        ∑ q : Green19H1.Q B.W, (Green19H1.cornersBox A B.W q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.cast_nonneg _
    have hReg_card_le : (Reg.card : ℝ) ≤ (Fintype.card (Green19H1.Q B.W) : ℝ) := by
      exact_mod_cast Finset.card_le_univ Reg
    have hL_eval : ∑ q ∈ Reg, (b * g (Green19H1.alphaBox A B.W q) - 8 * ε) * w ^ 3 =
        (b * (∑ q ∈ Reg, g (Green19H1.alphaBox A B.W q)) - 8 * ε * (Reg.card : ℝ)) * w ^ 3 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [mul_comm]
    rw [hL_eval] at hsum_reg
    have hcoeff : (Fintype.card (Green19H1.Q B.W) : ℝ) * (b * g α - (2 * b + 8) * ε) ≤
        b * (∑ q ∈ Reg, g (Green19H1.alphaBox A B.W q)) - 8 * ε * (Reg.card : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hReg_g hb.le
      have h2 : 8 * ε * (Reg.card : ℝ) ≤ 8 * ε * (Fintype.card (Green19H1.Q B.W) : ℝ) :=
        mul_le_mul_of_nonneg_left hReg_card_le (by positivity)
      linarith
    have hscale : (Fintype.card (Green19H1.Q B.W) : ℝ) * (b * g α - (2 * b + 8) * ε) * w ^ 3 ≤
        (b * (∑ q ∈ Reg, g (Green19H1.alphaBox A B.W q)) - 8 * ε * (Reg.card : ℝ)) * w ^ 3 :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hw_pos.le 3)
    have hQw3 : (Fintype.card (Green19H1.Q B.W) : ℝ) * w ^ 3 = N ^ 2 * w := by
      calc (Fintype.card (Green19H1.Q B.W) : ℝ) * w ^ 3
          = ((Fintype.card (Green19H1.Q B.W) : ℝ) * w ^ 2) * w := by ring
        _ = N ^ 2 * w := by rw [hQw2]
    have hrew : (Fintype.card (Green19H1.Q B.W) : ℝ) * (b * g α - (2 * b + 8) * ε) * w ^ 3 =
        (b * g α - (2 * b + 8) * ε) * N ^ 2 * w := by
      calc (Fintype.card (Green19H1.Q B.W) : ℝ) * (b * g α - (2 * b + 8) * ε) * w ^ 3
          = (b * g α - (2 * b + 8) * ε) * ((Fintype.card (Green19H1.Q B.W) : ℝ) * w ^ 3) := by ring
        _ = (b * g α - (2 * b + 8) * ε) * (N ^ 2 * w) := by rw [hQw3]
        _ = (b * g α - (2 * b + 8) * ε) * N ^ 2 * w := by ring
    linarith
  -- Step 6: Convert to ∑_{d ∈ W} |S d A|, subtract d = 0, and pigeonhole over W \ {0}.
  have hsum_S : ∑ d : B.W, ((Green19.S d.val A).card : ℝ) =
      ∑ q : Green19H1.Q B.W, (Green19H1.cornersBox A B.W q : ℝ) := by
    exact_mod_cast (Green19H1.sum_cornersBox_eq_sum_S A B.W).symm
  have hS0_le : ((Green19.S (0 : 𝔽₂ n) A).card : ℝ) ≤ N ^ 2 := by
    have hle : (Green19.S (0 : 𝔽₂ n) A).card ≤ Fintype.card (𝔽₂ n × 𝔽₂ n) := Finset.card_le_univ _
    rw [Fintype.card_prod] at hle
    have hcast : ((Green19.S (0 : 𝔽₂ n) A).card : ℝ) ≤ N * N := by dsimp only [N]; exact_mod_cast hle
    linarith
  have herase_sum : ∑ d ∈ (univ : Finset B.W).erase 0, ((Green19.S d.val A).card : ℝ) =
      (∑ d : B.W, ((Green19.S d.val A).card : ℝ)) - ((Green19.S (0 : 𝔽₂ n) A).card : ℝ) := by
    have h := Finset.add_sum_erase (univ : Finset B.W) (fun d : B.W => ((Green19.S d.val A).card : ℝ))
      (mem_univ 0)
    change ((Green19.S (0 : 𝔽₂ n) A).card : ℝ) +
      ∑ d ∈ (univ : Finset B.W).erase 0, ((Green19.S d.val A).card : ℝ) = _ at h
    linarith
  have hnonzero_sum : (b / 2) * α ^ c * N ^ 2 * (((univ : Finset B.W).erase 0).card : ℝ) ≤
      ∑ d ∈ (univ : Finset B.W).erase 0, ((Green19.S d.val A).card : ℝ) := by
    have h1 : (3 / 4 : ℝ) * b * α ^ c * N ^ 2 * w - N ^ 2 ≤
        ∑ d ∈ (univ : Finset B.W).erase 0, ((Green19.S d.val A).card : ℝ) := by
      have hscale : (3 / 4 : ℝ) * b * α ^ c * N ^ 2 * w ≤
          (b * g α - (2 * b + 8) * ε) * N ^ 2 * w :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε_good (sq_nonneg N)) hw_pos.le
      linarith
    have h2 : (1 : ℝ) ≤ (1 / 4 : ℝ) * b * α ^ c * w := by
      rwa [div_le_iff₀ hw_pos] at hinv_w
    have h3 : N ^ 2 ≤ (1 / 4 : ℝ) * b * α ^ c * N ^ 2 * w := by
      have := mul_le_mul_of_nonneg_left h2 (sq_nonneg N)
      linarith
    have h4 : (b / 2) * α ^ c * N ^ 2 * w ≤
        (3 / 4 : ℝ) * b * α ^ c * N ^ 2 * w - N ^ 2 := by linarith
    have hcard_le : (((univ : Finset B.W).erase 0).card : ℝ) ≤ w := by
      dsimp only [w]; exact_mod_cast Finset.card_le_univ ((univ : Finset B.W).erase 0)
    have h5 : (b / 2) * α ^ c * N ^ 2 * (((univ : Finset B.W).erase 0).card : ℝ) ≤
        (b / 2) * α ^ c * N ^ 2 * w :=
      mul_le_mul_of_nonneg_left hcard_le (by positivity)
    linarith
  have hne : ((univ : Finset B.W).erase 0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hcard : ((univ : Finset B.W).erase 0).card = Fintype.card B.W - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ]
    rw [hemp, Finset.card_empty] at hcard
    have hcard_le1 : Fintype.card B.W ≤ 1 := by omega
    have hw_le1 : w ≤ 1 := by dsimp only [w]; exact_mod_cast hcard_le1
    linarith
  by_contra hall
  push Not at hall
  have hlt : ∑ d ∈ (univ : Finset B.W).erase 0, ((Green19.S d.val A).card : ℝ) <
      ∑ _d ∈ (univ : Finset B.W).erase 0, ((b / 2) * α ^ c * N ^ 2) := by
    refine Finset.sum_lt_sum_of_nonempty hne fun d hd => ?_
    have hd0 : d.val ≠ 0 := fun hz => (Finset.mem_erase.mp hd).1 (Subtype.ext hz)
    exact hall d.val hd0
  simp only [Finset.sum_const, nsmul_eq_mul] at hlt
  linarith

end


section

-- Credit: @marcusbuffett
/-! A random coloring of the three vertex classes realizes the triangle template. A fourth-moment bounded-differences estimate controls all nonzero directions simultaneously. -/
open Finset Filter
open scoped Classical BigOperators
namespace GreenSample
variable {V : Type*} [Fintype V] [Nonempty V]
private lemma eprod {U W : Type*} [Fintype U] [Fintype W] (f : U × W → ℝ) :
    (𝔼 a, f a) = 𝔼 u, 𝔼 w, f (u,w) := by
  simpa using expect_product (univ : Finset U) (univ : Finset W) f

private lemma echead {n : ℕ} (f : (Fin (n+1) → V) → ℝ) :
    (𝔼 a, f a) = 𝔼 t : Fin n → V, 𝔼 v : V, f (Fin.cons v t) := by
  let e : ((Fin n → V) × V) ≃ (Fin (n+1) → V) :=
    { toFun := fun p ↦ Fin.cons p.2 p.1
      invFun := fun a ↦ (fun i ↦ a i.succ, a 0)
      left_inv := fun p ↦ by simp
      right_inv := fun a ↦ by ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }
  rw [← Fintype.expect_equiv e (fun p ↦ f (e p)) f (fun _ ↦ rfl), eprod]
  rfl

private lemma abs_mean {U : Type*} [Fintype U] [Nonempty U] {f g : U → ℝ} {L : ℝ}
    (h : ∀ u, |f u - g u| ≤ L) : |(𝔼 u, f u) - 𝔼 u, g u| ≤ L := by
  rw [← expect_sub_distrib]
  exact (abs_expect_le _ _).trans (expect_le univ_nonempty fun u _ ↦ h u)

private lemma conditional {U : Type*} [Fintype U] [Nonempty U] (a L : ℝ) (b : U → ℝ)
    (hb : ∀ u, |b u| ≤ L) (hz : (𝔼 u, b u) = 0) :
    (𝔼 u, (a+b u)^2) ≤ a^2 + L^2 ∧
    (𝔼 u, (a+b u)^4) ≤ a^4 + 8*L^2*a^2 + 3*L^4 := by
  have bs (u) : (b u)^2 ≤ L^2 := by
    have h := abs_le.mp (hb u)
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ L + b u by linarith [h.1])]
  have bq (u) : (b u)^4 ≤ L^4 := by nlinarith [sq_le_sq' (show -(L^2) ≤ (b u)^2 by nlinarith [sq_nonneg (b u), sq_nonneg L]) (bs u)]
  constructor
  · calc
      _ ≤ 𝔼 u, (a^2 + L^2 + (2*a)*b u) := expect_le_expect fun u _ ↦ by nlinarith [bs u]
      _ = _ := by rw [expect_add_distrib, ← mul_expect]; simp [hz]
  · calc
      _ ≤ 𝔼 u, (a^4 + 8*L^2*a^2 + 3*L^4 + (4*a^3)*b u) := expect_le_expect fun u _ ↦ by
        nlinarith [sq_nonneg (a*b u - (b u)^2), bq u, mul_le_mul_of_nonneg_right (bs u) (sq_nonneg a)]
      _ = _ := by rw [expect_add_distrib, ← mul_expect]; simp [hz]

lemma boundedMoments {n : ℕ} (f : (Fin n → V) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (osc : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ L) :
    (𝔼 x, (f x - 𝔼 z, f z)^2) ≤ n * L^2 ∧
    (𝔼 x, (f x - 𝔼 z, f z)^4) ≤ 4*(n:ℝ)^2 * L^4 := by
  classical
  induction n with
  | zero =>
    have eq : ∀ x : Fin 0 → V, f x = f (fun i ↦ i.elim0) := fun x ↦ congrArg f (Subsingleton.elim _ _)
    simp [eq]
  | succ n ih =>
    let g := fun t : Fin n → V ↦ 𝔼 v : V, f (Fin.cons v t)
    let m := 𝔼 t, g t
    have hmean : (𝔼 z, f z) = m := echead f
    have gosc (i : Fin n) (x y : Fin n → V) (h : ∀ j, j ≠ i → x j = y j) : |g x-g y| ≤ L := by
      apply abs_mean
      intro v
      apply osc i.succ
      intro j
      refine Fin.cases (by simp) (fun k hk ↦ ?_) j
      simpa using h k (fun he ↦ hk (congrArg Fin.succ he))
    obtain ⟨ig2,ig4⟩ := ih g gosc
    have cb (t : Fin n → V) (v : V) : |f (Fin.cons v t)-g t| ≤ L := by
      have h (w : V) : |f (Fin.cons v t)-f (Fin.cons w t)| ≤ L := by
        apply osc 0
        intro j
        refine Fin.cases (by simp) (fun k _ ↦ by simp) j
      simpa only [g, Fintype.expect_const] using abs_mean h
    have bound (t : Fin n → V) :=
      conditional (g t-m) L (fun v ↦ f (Fin.cons v t)-g t) (cb t) (by simp [expect_sub_distrib,g])
    have c2 (t : Fin n → V) : (𝔼 v, (f (Fin.cons v t)-m)^2) ≤ (g t-m)^2 + L^2 := by
      simpa only [sub_add_sub_cancel'] using (bound t).1
    have c4 (t : Fin n → V) : (𝔼 v, (f (Fin.cons v t)-m)^4) ≤ (g t-m)^4 + 8*L^2*(g t-m)^2 + 3*L^4 := by
      simpa only [sub_add_sub_cancel'] using (bound t).2
    change (𝔼 x, (g x-m)^2) ≤ _ at ig2
    change (𝔼 x, (g x-m)^4) ≤ _ at ig4
    rw [hmean, echead, echead (fun x ↦ (f x-m)^4)]
    constructor
    · calc
        _ ≤ 𝔼 t, ((g t-m)^2 + L^2) := expect_le_expect fun t _ ↦ c2 t
        _ ≤ _ := by rw [expect_add_distrib, Fintype.expect_const]; push_cast; linarith
    · calc
        _ ≤ 𝔼 t, ((g t-m)^4 + 8*L^2*(g t-m)^2 + 3*L^4) := expect_le_expect fun t _ ↦ c4 t
        _ ≤ _ := by
          simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, Nat.cast_succ]
          nlinarith [mul_le_mul_of_nonneg_left ig2 (show 0 ≤ 8*L^2 by positivity), sq_nonneg (L^2)]
lemma momentsAny {I : Type*} [Fintype I] [DecidableEq I] (f : (I → V) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (osc : ∀ (i : I) x y, (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ L) :
    (𝔼 x, (f x - 𝔼 z, f z)^4) ≤ 4*(Fintype.card I : ℝ)^2 * L^4 := by
  let e := Fintype.equivFin I
  let E := e.arrowCongr (Equiv.refl V)
  let g := fun u ↦ f (E.symm u)
  have he (u : Fin (Fintype.card I) → V) (i : I) : E.symm u i = u (e i) := rfl
  have hosc (i : Fin (Fintype.card I)) (x y : Fin (Fintype.card I) → V)
      (h : ∀ j, j ≠ i → x j = y j) : |g x-g y| ≤ L := by
    apply osc (e.symm i)
    intro j hj
    exact h (e j) (fun eq ↦ hj (e.apply_eq_iff_eq_symm_apply.mp eq))
  have hg := (boundedMoments g L hL hosc).2
  have avg : (𝔼 x, f x) = 𝔼 u, g u := Fintype.expect_equiv E _ _ (fun x ↦ by simp [g])
  rw [avg, Fintype.expect_equiv E _ (fun u ↦ (g u - 𝔼 z, g z)^4) (fun x ↦ by simp [g])]
  exact hg

lemma simultaneous {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] (F : K → (I → V) → ℝ)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (osc : ∀ k (i : I) x y, (∀ j, j ≠ i → x j = y j) → |F k x-F k y| ≤ L)
    (big : (Fintype.card K : ℝ)*(4*(Fintype.card I : ℝ)^2 * L^4) < T^4) :
    ∃ x, ∀ k, |F k x - 𝔼 z, F k z| < T := by
  classical
  have av : (𝔼 x, ∑ k, (F k x - 𝔼 z, F k z)^4) ≤
      (Fintype.card K : ℝ)*(4*(Fintype.card I : ℝ)^2*L^4) := by
    rw [expect_sum_comm]
    simpa using sum_le_sum (s := (univ : Finset K)) (fun k _ ↦ momentsAny (F k) L hL (osc k))
  obtain ⟨x,_,hx⟩ := exists_le_of_expect_le univ_nonempty av
  refine ⟨x, fun k ↦ ?_⟩
  have b := single_le_sum (s := (univ : Finset K)) (f := fun k ↦ (F k x - 𝔼 z, F k z)^4)
      (fun i _ ↦ by positivity) (mem_univ k)
  by_contra! h
  have := pow_le_pow_left₀ hT.le h 4
  rw [← abs_pow, abs_of_nonneg (by positivity)] at this
  linarith

lemma marginal {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (u : J ↪ I) (H : (J → V) → ℝ) :
    (𝔼 x : I → V, H (fun j ↦ x (u j))) = 𝔼 z, H z := by
  classical
  let s := Set.range u
  let e := Equiv.ofInjective u u.injective
  let e₁ := Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ s) (fun _ ↦ V)
  let e₂ := e.symm.arrowCongr (Equiv.refl V)
  let E := e₁.trans (e₂.prodCongr (Equiv.refl _))
  have he (x : I → V) : (E x).1 = fun j ↦ x (u j) := rfl
  rw [Fintype.expect_equiv E _ (fun pair ↦ H pair.1) (fun x ↦ by rw [he]), eprod]
  simp [Fintype.expect_const]

noncomputable def countSample {U I J : Type*} [Fintype U]
    (coord : U → J → I) (H : (J → V) → Prop) (f : I → V) : ℝ :=
  ∑ p : U, if H (fun j ↦ f (coord p j)) then 1 else 0

lemma meanSample {U I J : Type*} [Fintype U] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (coord : U → J → I) (hi : ∀ p, Function.Injective (coord p)) (H : (J → V) → Prop) :
    (𝔼 f, countSample coord H f) =
    (Fintype.card U : ℝ) * (((univ : Finset (J → V)).filter H).card / (Fintype.card V : ℝ)^(Fintype.card J)) := by
  classical
  unfold countSample
  rw [expect_sum_comm]
  have hh (p : U) := marginal (V := V) (⟨_,hi p⟩ : J ↪ I) (fun z ↦ if H z then (1:ℝ) else 0)
  simp only [Function.Embedding.coeFn_mk] at hh
  simp_rw [hh]
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fintype.card_fun, Nat.cast_pow, Finset.sum_boole]

lemma oscSample {U I J : Type*} [Fintype U] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (coord : U → J → I) (H : (J → V) → Prop) (M : ℕ)
    (hM : ∀ j i, ((univ : Finset U).filter (fun p ↦ coord p j = i)).card ≤ M)
    (i : I) (x y : I → V) (hxy : ∀ j, j ≠ i → x j = y j) :
    |countSample coord H x-countSample coord H y| ≤ (Fintype.card J : ℝ)*M := by
  classical
  unfold countSample
  rw [← sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ p : U, ∑ j : J, if coord p j = i then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro p _
      by_cases hb : ∃ j, coord p j = i
      · obtain ⟨j,hj⟩ := hb
        have h := single_le_sum (s := (univ : Finset J))
          (f := fun j ↦ if coord p j = i then (1:ℝ) else 0) (fun k _ ↦ by split <;> norm_num) (mem_univ j)
        rw [if_pos hj] at h
        split_ifs <;> norm_num at * <;> assumption
      · have same : (fun j ↦ x (coord p j)) = (fun j ↦ y (coord p j)) :=
          funext fun j ↦ hxy _ (fun he ↦ hb ⟨_,he⟩)
        rw [same, sub_self, abs_zero]
        exact sum_nonneg (fun j _ ↦ by split <;> norm_num)
    _ = ∑ j : J, (((univ : Finset U).filter (fun p ↦ coord p j = i)).card : ℝ) := by rw [sum_comm]; simp [Finset.sum_boole]
    _ ≤ ∑ _ : J, (M : ℝ) := sum_le_sum fun j _ ↦ by exact_mod_cast hM j i
    _ = _ := by simp

end GreenSample

open Finset Filter
open scoped Classical BigOperators
namespace GreenSample
variable {V : Type*} [Fintype V] [DecidableEq V]
def triangle (G : SimpleGraph V) (a b c : V) := G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
def densityEvent (G : SimpleGraph V) (u : Fin 3 → V) := triangle G (u 0) (u 1) (u 2)
def cornerEvent (G : SimpleGraph V) (u : Fin 6 → V) :=
  triangle G (u 0) (u 1) (u 2) ∧ triangle G (u 3) (u 1) (u 5) ∧ triangle G (u 0) (u 4) (u 5)

lemma uniqueThird {G : SimpleGraph V} (hl : G.LocallyLinear) {a b c d : V}
    (hc : triangle G a b c) (hd : triangle G a b d) : c = d := by
  obtain ⟨hab,hac,hbc⟩ := hc
  obtain ⟨_,had,hbd⟩ := hd
  have eq : ({a,b,c} : Finset V) = {a,b,d} := by
    apply hl.1.eq (by simp [SimpleGraph.is3Clique_triple_iff, *]) (by simp [SimpleGraph.is3Clique_triple_iff, *])
    exact Set.Nontrivial.not_subsingleton ⟨a, by simp, b, by simp, hab.ne⟩
  have h : c ∈ ({a,b,d} : Finset V) := eq ▸ (by simp)
  simpa [hac.ne', hbc.ne'] using h

lemma congrCorner {G : SimpleGraph V} (hl : G.LocallyLinear) {u : Fin 6 → V} (h : cornerEvent G u) :
    u 2 = u 5 ∧ u 3 = u 0 ∧ u 4 = u 1 := by
  obtain ⟨ha,hb,hc⟩ := h
  have t : triangle G (u 0) (u 1) (u 5) := ⟨ha.1,hc.2.1,hb.2.2⟩
  refine ⟨uniqueThird hl ha t, ?_, ?_⟩
  · exact uniqueThird (a := u 1) (b := u 5) hl ⟨hb.2.2,hb.1.symm,hb.2.1.symm⟩ ⟨t.2.2,t.1.symm,t.2.1.symm⟩
  · exact uniqueThird (a := u 0) (b := u 5) hl ⟨hc.2.1,hc.1,hc.2.2.symm⟩ ⟨t.2.1,t.1,t.2.2.symm⟩

lemma cornerCard (G : SimpleGraph V) (hl : G.LocallyLinear) :
    ((univ : Finset (Fin 6 → V)).filter (cornerEvent G)).card ≤ (Fintype.card V)^2 := by
  let S := (univ : Finset (Fin 6 → V)).filter (cornerEvent G)
  let F (u : S) : V × V := (u.val 0, u.val 1)
  have inj : Function.Injective F := by
    intro u v e
    have hu := (mem_filter.mp u.property).2
    have hv := (mem_filter.mp v.property).2
    have eq0 : u.val 0 = v.val 0 := congrArg Prod.fst e
    have eq1 : u.val 1 = v.val 1 := congrArg Prod.snd e
    have eq2 : u.val 2 = v.val 2 := uniqueThird hl hu.1 (by rw [eq0,eq1]; exact hv.1)
    obtain ⟨ua,ub,uc⟩ := congrCorner hl hu
    obtain ⟨va,vb,vc⟩ := congrCorner hl hv
    apply Subtype.ext
    funext i
    fin_cases i <;> simp_all
  simpa only [Fintype.card_coe,S,Fintype.card_prod,pow_two] using Fintype.card_le_of_injective F inj

lemma densityCard (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (G.cliqueFinset 3).card ≤ ((univ : Finset (Fin 3 → V)).filter (densityEvent G)).card := by
  let C := ↥(G.cliqueFinset 3)
  have rep (s : C) : ∃ a b c, triangle G a b c ∧ s.val = {a,b,c} := by
    obtain ⟨a,b,c,hab,hac,hbc,e⟩ := SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp s.property)
    exact ⟨a,b,c,⟨hab,hac,hbc⟩,e⟩
  choose a b c tr he using rep
  let P := (univ : Finset (Fin 3 → V)).filter (densityEvent G)
  let f (p : Bool × C) : Fin 3 → V := if p.1 then ![b p.2,a p.2,c p.2] else ![a p.2,b p.2,c p.2]
  have hf (p : Bool × C) : f p ∈ P := by
    obtain ⟨flag,s⟩ := p
    obtain ⟨hab,hac,hbc⟩ := tr s
    cases flag <;> simp [P,f,densityEvent,triangle,hab,hac,hbc,hab.symm]
  let F (p : Bool × C) : P := ⟨f p,hf p⟩
  have recover (p : Bool × C) : ({f p 0,f p 1,f p 2} : Finset V) = p.2.val := by
    obtain ⟨flag,s⟩ := p
    cases flag <;> simp [f,he s,Finset.insert_comm]
  have inj : Function.Injective F := by
    rintro ⟨b₁,s⟩ ⟨b₂,t⟩ eq
    have ev : f (b₁,s) = f (b₂,t) := congrArg Subtype.val eq
    have eqs : s = t := Subtype.ext ((recover (b₁,s)).symm.trans ((congrArg (fun v : Fin 3 → V ↦ ({v 0,v 1,v 2} : Finset V)) ev).trans (recover (b₂,t))))
    subst t
    have first := congrFun ev 0
    have ne := (tr s).1.ne
    cases b₁ <;> cases b₂ <;> simp_all [f]
  simpa only [C,P,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] using Fintype.card_le_of_injective F inj
end GreenSample

open Finset Filter
open scoped Classical BigOperators
namespace GreenSample
variable {W : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
def coord3 (p : W × W) : Fin 3 → Fin 3 × W := ![(0,p.1), (1,p.2), (2,p.1+p.2)]
def coord6 (d : W) (p : W × W) : Fin 6 → Fin 3 × W :=
  ![(0,p.1), (1,p.2), (2,p.1+p.2), (0,p.1+d), (1,p.2+d), (2,p.1+p.2+d)]

lemma coord3inj (p : W × W) : Function.Injective (coord3 p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coord3]
lemma coord6inj {d : W} (hd : d ≠ 0) (p : W × W) : Function.Injective (coord6 d p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coord6]

private lemma lineBound (k : Fin 3) (t : W) (i : Fin 3 × W) :
    ((univ : Finset (W × W)).filter (fun p ↦
      (k, (![p.1,p.2,p.1+p.2] k)+t) = i)).card ≤ Fintype.card W := by
  classical
  let S := (univ : Finset (W × W)).filter (fun p ↦ (k, (![p.1,p.2,p.1+p.2] k)+t) = i)
  let key (x : S) := if k = 0 then x.val.2 else x.val.1
  have inj : Function.Injective key := by
    rintro ⟨⟨x,y⟩,hx⟩ ⟨⟨x',y'⟩,hy⟩ eq
    have ev := congrArg Prod.snd (((mem_filter.mp hx).2).trans (mem_filter.mp hy).2.symm)
    fin_cases k <;> simp_all [key]
  simpa only [S,Fintype.card_coe] using Fintype.card_le_of_injective key inj

lemma bound3 (j : Fin 3) (i : Fin 3 × W) :
    ((univ : Finset (W × W)).filter (fun p ↦ coord3 p j = i)).card ≤ Fintype.card W := by
  fin_cases j
  · convert! lineBound 0 (0:W) i using 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coord3]
  · convert! lineBound 1 (0:W) i using 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coord3]
  · convert! lineBound 2 (0:W) i using 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coord3]

lemma bound6 (d : W) (j : Fin 6) (i : Fin 3 × W) :
    ((univ : Finset (W × W)).filter (fun p ↦ coord6 d p j = i)).card ≤ Fintype.card W := by
  fin_cases j
  · convert! lineBound 0 (0:W) i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 1 (0:W) i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 2 (0:W) i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 0 d i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 1 d i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
  · convert! lineBound 2 d i using 1
    all_goals congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp [coord6]
end GreenSample

namespace GreenSample
open Filter Finset
open scoped Classical BigOperators
variable {W V : Type*} [AddCommGroup W] [Fintype W] [Fintype V]

noncomputable def vertexSet (G : SimpleGraph V) (x : Fin 3 × W → V) : Finset (W × W) :=
  univ.filter (fun p ↦ densityEvent G (fun j ↦ x (coord3 p j)))

lemma sample3eq (G : SimpleGraph V) (x : Fin 3 × W → V) :
    countSample coord3 (densityEvent G) x = ((vertexSet G x).card : ℝ) := by
  simp [countSample,vertexSet,sum_boole]

lemma sample6eq (G : SimpleGraph V) (x : Fin 3 × W → V) (d : W) :
    countSample (coord6 d) (cornerEvent G) x = ((Green19.S d (vertexSet G x)).card : ℝ) := by
  classical
  simp only [countSample,sum_boole]
  apply congrArg (fun s : Finset (W × W) ↦ (s.card : ℝ))
  have mv (p : W × W) : p ∈ vertexSet G x ↔ densityEvent G (fun j ↦ x (coord3 p j)) := by
    unfold vertexSet
    exact (@Finset.mem_filter _ _ _ _ _).trans (and_iff_right (mem_univ p))
  ext p
  unfold Green19.S
  rw [Finset.mem_filter,Finset.mem_filter]
  simp only [mem_univ,true_and,Green19.IsCorner,mv,cornerEvent,densityEvent]
  simp [coord3,coord6,add_assoc,add_comm,add_left_comm]

end GreenSample

open GreenSample Filter Finset
open scoped Classical BigOperators
theorem OMA.cornersUpper : OMA.R_Green19_green_19_R1.H2 := by
  classical
  intro q hq G _ hl
  haveI : NeZero q := ⟨by omega⟩
  have qp : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_gt_atTop (46656*q^16)] with n hn
  let W := 𝔽₂ n
  let N : ℝ := Fintype.card W
  have np : 0 < N := by dsimp [N]; positivity
  let t : ℝ := (G.cliqueFinset 3).card
  by_cases ht : (G.cliqueFinset 3).card = 0
  · refine ⟨∅, ?_, fun d _ ↦ ?_⟩
    · simp [ht]
    · simp [Green19.S,Green19.IsCorner]; positivity
  have tp : 1 ≤ t := by dsimp [t]; exact_mod_cast (show 1 ≤ (G.cliqueFinset 3).card by omega)
  have cardW : Fintype.card W = 2^n := by simp [W,𝔽₂,𝔽,Fintype.card_fun]
  have alln (m : ℕ) : m < 2^m := by induction m with | zero => simp | succ m ih => rw [pow_succ]; omega
  have hn2 := alln n
  have large : 46656 * (q : ℝ)^16 < N := by
    dsimp only [N]
    exact_mod_cast (show 46656*q^16 < Fintype.card W by rw [cardW]; omega)
  let F (d : W) (f : Fin 3 × W → Fin q) :=
    if d = 0 then countSample coord3 (densityEvent G) f else countSample (coord6 d) (cornerEvent G) f
  let T := N^2 / (q:ℝ)^4
  have Tpos : 0 < T := by dsimp [T]; positivity
  have os (d : W) (i : Fin 3 × W) (f g : Fin 3 × W → Fin q) (h : ∀ j, j ≠ i → f j = g j) :
      |F d f - F d g| ≤ 6*N := by
    by_cases hd : d = 0
    · simpa [F,hd] using (oscSample coord3 (densityEvent G) (Fintype.card W) (bound3 (W := W)) i f g h).trans
        (show (Fintype.card (Fin 3):ℝ)*Fintype.card W ≤ 6*N by simp only [Fintype.card_fin,Nat.cast_ofNat]; change 3*N ≤ 6*N; linarith)
    · simpa [F,hd,N] using oscSample (coord6 d) (cornerEvent G) (Fintype.card W) (bound6 d) i f g h
  have big : (Fintype.card W : ℝ)*(4*(Fintype.card (Fin 3 × W):ℝ)^2*(6*N)^4) < T^4 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    change N*(4*(3*N)^2*(6*N)^4) < (N^2/(q:ℝ)^4)^4
    rw [div_pow, lt_div_iff₀ (by positivity)]
    nlinarith only [mul_lt_mul_of_pos_right large (show 0 < N^7 by positivity)]
  obtain ⟨f,good⟩ := simultaneous (V := Fin q) F (L := 6*N) (T := T) (by positivity) Tpos os big
  have h3 := meanSample (V := Fin q) (@coord3 W _ ) coord3inj (densityEvent G)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at h3
  have dg := good 0
  simp only [F,if_true] at dg
  rw [h3] at dg
  have lo := (abs_lt.mp dg).1
  have ca : 2*t ≤ (((univ : Finset (Fin 3 → Fin q)).filter (densityEvent G)).card : ℝ) := by dsimp [t]; exact_mod_cast densityCard G
  have lomean : N*N * (2*t/(q:ℝ)^3) ≤ N*N * ((((univ : Finset (Fin 3 → Fin q)).filter (densityEvent G)).card : ℝ)/(q:ℝ)^3) := by gcongr
  have margin : T ≤ (t/(q:ℝ)^3)*N^2 := by
    change N^2 / (q:ℝ)^4 ≤ _
    field_simp
    have qr : 1 ≤ (q:ℝ) := by exact_mod_cast hq.le
    exact one_le_mul_of_one_le_of_one_le qr tp
  refine ⟨vertexSet G f, ?_, ?_⟩
  · change t / (q:ℝ)^3 * N^2 ≤ _
    rw [← sample3eq]
    change -T < countSample coord3 (densityEvent G) f - N*N*(_/(q:ℝ)^3) at lo
    have hh : t/(q:ℝ)^3*N^2 + T ≤ N*N*(2*t/(q:ℝ)^3) := calc
      _ ≤ t/(q:ℝ)^3*N^2 + t/(q:ℝ)^3*N^2 := add_le_add_right margin _
      _ = _ := by ring
    linarith only [lo,hh.trans lomean]
  · intro d hd
    have h6 := meanSample (V := Fin q) (coord6 d) (coord6inj hd) (cornerEvent G)
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at h6
    have ug := good d
    simp only [F,if_neg hd] at ug
    rw [h6] at ug
    have hi := (abs_lt.mp ug).2
    have ca6 : (((univ : Finset (Fin 6 → Fin q)).filter (cornerEvent G)).card : ℝ) ≤ (q:ℝ)^2 := by
      simpa only [Fintype.card_fin] using (show (((univ : Finset (Fin 6 → Fin q)).filter (cornerEvent G)).card : ℝ) ≤ (Fintype.card (Fin q) : ℝ)^2 by exact_mod_cast cornerCard G hl)
    have up : N*N * ((((univ : Finset (Fin 6 → Fin q)).filter (cornerEvent G)).card : ℝ)/(q:ℝ)^6) ≤ T := calc
      _ ≤ N*N * ((q:ℝ)^2/(q:ℝ)^6) := by gcongr
      _ = _ := by dsimp [T]; field_simp <;> ring
    rw [← sample6eq]
    change countSample (coord6 d) (cornerEvent G) f ≤ (2/(q:ℝ)^4)*N^2
    change countSample (coord6 d) (cornerEvent G) f - N*N*(_/(q:ℝ)^6) < T at hi
    calc
      _ ≤ T+T := by linarith only [up,hi]
      _ = _ := by dsimp [T]; ring

end

theorem OMA.solution : type_of% @Green19.green_19 :=
  OMA.R_Green19_green_19_R1.main OMA.cornersLower OMA.cornersUpper
