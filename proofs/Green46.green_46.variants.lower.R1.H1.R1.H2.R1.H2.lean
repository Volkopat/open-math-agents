import OMAReductions.R_Green46_green_46_variants_lower_R1_H1_R1_H2_R1
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset
open scoped BigOperators

namespace GreenPartition

theorem vertex_bound (P V : Finset ℕ) (E : ℕ → Finset (Finset ℕ))
    (w : ℕ → Finset ℕ → ℝ) (B : ℝ)
    (hsize : ∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card : ℝ) ≤ B)
    (hw : ∀ p ∈ P, (∑ e ∈ E p, w p e) = 1 ∧ ∀ e ∈ E p, 0 ≤ w p e)
    (hdeg : ∀ q ∈ V, 1 ≤ ∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e) :
    (V.card : ℝ) ≤ P.card * B := by
  classical
  calc
    (V.card : ℝ) = ∑ q ∈ V, (1 : ℝ) := by simp
    _ ≤ ∑ q ∈ V, ∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e := sum_le_sum hdeg
    _ = ∑ p ∈ P, ∑ q ∈ V, ∑ e ∈ (E p).filter (q ∈ ·), w p e := sum_comm
    _ ≤ ∑ p ∈ P, B := by
      apply sum_le_sum
      intro p hp
      simp_rw [sum_filter]
      rw [sum_comm]
      calc
        _ = ∑ e ∈ E p, (e.card : ℝ) * w p e := by
          apply sum_congr rfl
          intro e he
          rw [← sum_filter]
          have h : V.filter (· ∈ e) = e := by
            ext q
            simp only [mem_filter]
            exact ⟨And.right, fun hq => ⟨(hsize p hp e he).1 hq, hq⟩⟩
          simp [h]
        _ ≤ ∑ e ∈ E p, B * w p e := sum_le_sum fun e he =>
          mul_le_mul_of_nonneg_right (hsize p hp e he).2 ((hw p hp).2 e he)
        _ = B := by rw [← mul_sum, (hw p hp).1, mul_one]
    _ = _ := by simp

end GreenPartition

namespace GreenPartition
open MeasureTheory ProbabilityTheory

theorem uniform_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} (A : Finset ι) {X : ι → Ω → ℝ} {b ε : ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i ∈ A, AEMeasurable (X i) μ)
    (hb : ∀ i ∈ A, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 b) (he : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ A, (X i ω - ∫ t, X i t ∂μ)} ≤
      Real.exp (-ε ^ 2 / (2 * ((A.card : ℝ) * ((‖b‖ / 2)^2)))) := by
  classical
  have hind := hi.comp (fun i (x : ℝ) => x - ∫ t, X i t ∂μ)
    (fun _ => measurable_id.sub_const _)
  have hg (i) (hi : i ∈ A) := hasSubgaussianMGF_of_mem_Icc (hm i hi) (hb i hi)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := A) (fun i h => hg i h) he
  simpa [Function.comp_def] using h

end GreenPartition

namespace GreenPartition
open MeasureTheory ProbabilityTheory

theorem abs_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} (A : Finset ι) {X : ι → Ω → ℝ} {b ε : ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i ∈ A, AEMeasurable (X i) μ)
    (hb : ∀ i ∈ A, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 b) (he : 0 ≤ ε) :
    μ.real {ω | ε < |∑ i ∈ A, (X i ω - ∫ t, X i t ∂μ)|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((A.card : ℝ) * ((‖b‖ / 2)^2)))) := by
  classical
  let Y i ω := X i ω - ∫ t, X i t ∂μ
  have hind : iIndepFun Y μ := hi.comp (fun i (x : ℝ) => x - ∫ t, X i t ∂μ)
    (fun _ => measurable_id.sub_const _)
  have hn := hind.comp (fun _ (x : ℝ) => -x) (fun _ => measurable_neg)
  have hg (i) (hi : i ∈ A) := (hasSubgaussianMGF_of_mem_Icc (hm i hi) (hb i hi)).neg
  have hneg := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hn (s := A) (fun i h => hg i h) he
  have hp := uniform_tail μ A hi hm hb he
  let pos := {ω | ε ≤ ∑ i ∈ A, Y i ω}
  let neg := {ω | ε ≤ -(∑ i ∈ A, Y i ω)}
  have hn' : μ.real neg ≤ Real.exp (-ε^2 / (2 * (A.card * (‖b‖ / 2)^2))) := by simpa [neg, Function.comp_def, Y] using hneg
  have hsub : {ω | ε < |∑ i ∈ A, Y i ω|} ⊆ pos ∪ neg := by
    intro ω h
    change ε < |∑ i ∈ A, Y i ω| at h
    rcases lt_abs.mp h with h | h
    · exact Or.inl h.le
    · exact Or.inr (by dsimp [neg]; linarith)
  have hu := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le pos neg)
  change μ.real pos ≤ _ at hp
  exact hu.trans (by linarith)

end GreenPartition

namespace GreenPartition

noncomputable def roundLaw {J : Type*} [Fintype J] (s : J → ℝ)
    (hs : ∀ j, 0 ≤ s j) (ht : ∑ j, s j ≤ 1) : PMF (Option J) := by
  let a : Option J → ℝ := fun t => t.elim (1 - ∑ j, s j) s
  have ha : ∀ t, 0 ≤ a t := by
    rintro (_ | j)
    · exact sub_nonneg.mpr ht
    · exact hs j
  apply PMF.ofFintype (fun t => ENNReal.ofReal (a t))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => ha t), Fintype.sum_option]
  simp [a]

@[simp] theorem roundLaw_some {J : Type*} [Fintype J] (s : J → ℝ)
    (hs : ∀ j, 0 ≤ s j) (ht : ∑ j, s j ≤ 1) (j : J) :
    roundLaw s hs ht (some j) = ENNReal.ofReal (s j) := rfl

end GreenPartition

namespace GreenPartition
open MeasureTheory

theorem coordinate_mean {J P : Type*} [Fintype J] [DecidableEq J] [Fintype P]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (s : J → ℝ) (hs : ∀ j, 0 ≤ s j) (ht : ∑ j, s j ≤ 1) (j : J) (p : P) (a : ℝ) :
    (∫ ω : P → Option J, (if ω p = some j then a else 0)
      ∂Measure.pi (fun _ : P => (roundLaw s hs ht).toMeasure)) = s j * a := by
  classical
  let f (t : Option J) : ℝ := if t = some j then a else 0
  have hm : Measurable f := measurable_of_finite _
  change (∫ ω : P → Option J, f (ω p) ∂_) = _
  rw [integral_comp_eval hm.aestronglyMeasurable, PMF.integral_eq_sum]
  simp [f, hs j]

end GreenPartition

namespace GreenPartition
open MeasureTheory

theorem exists_good_sample {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Finset ι) (bad : ι → Set Ω) (δ : ℝ)
    (hbad : ∀ i ∈ A, μ.real (bad i) ≤ δ) (hsmall : A.card * δ < 1) :
    ∃ ω, ∀ i ∈ A, ω ∉ bad i := by
  classical
  by_contra! h
  have hall : (⋃ i ∈ A, bad i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨i, hi, hω⟩ := h ω
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hω⟩
  have hle := measureReal_biUnion_finset_le (μ := μ) A bad
  rw [hall] at hle
  have hs := Finset.sum_le_sum hbad
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  exact (not_lt_of_ge (by simpa using hle.trans hs)) hsmall

end GreenPartition

namespace GreenPartition
open Filter Real
open scoped Topology

theorem eventually_round_margin :
    ∀ᶠ x : ℕ in atTop, 1 ≤ log (log (x : ℝ)) ∧
      4 * log (x : ℝ) * (log (log (x : ℝ)))^4 ≤ (x : ℝ)^(1/5 : ℝ) := by
  have hg := (isLittleO_log_rpow_rpow_atTop 5 (by norm_num : 0 < (1/5 : ℝ))).bound
    (by norm_num : 0 < (1/4 : ℝ))
  have ht := (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hg, ht,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with x hx hu hl
  simp only [Function.comp_apply] at hu hl
  refine ⟨hu, ?_⟩
  have hu' : log (log (x : ℝ)) ≤ log (x : ℝ) := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h5 : (log (x : ℝ)) ^ 5 ≤ (1 / 4 : ℝ) * (x : ℝ) ^ (1 / 5 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg, Real.rpow_nonneg (Nat.cast_nonneg x),
      Real.rpow_natCast, show 0 ≤ log (x : ℝ) by linarith] using hx
  calc
    _ ≤ 4 * log (x : ℝ) * (log (x : ℝ)) ^ 4 := by gcongr
    _ ≤ _ := by linarith [show 4 * log (x : ℝ) * log (x : ℝ)^4 = 4 * log (x : ℝ)^5 by ring]

end GreenPartition
namespace GreenPartition
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem finite_round {P J V : Type*} [Fintype P] [Fintype J] [DecidableEq J] [Fintype V]
    (a : P → V → ℝ) (s : J → ℝ) {b ε : ℝ}
    (ha : ∀ p q, a p q ∈ Set.Icc 0 b) (hs : ∀ j, 0 ≤ s j) (ht : ∑ j, s j ≤ 1)
    (he : 0 ≤ ε)
    (hsmall : (Fintype.card (J × V) : ℝ) *
      (2 * Real.exp (-ε^2 / (2 * (Fintype.card P * (‖b‖/2)^2)))) < 1) :
    ∃ f : P → Option J, ∀ j q,
      |(∑ p, if f p = some j then a p q else 0) - s j * ∑ p, a p q| ≤ ε := by
  classical
  letI : MeasurableSpace (Option J) := ⊤
  letI : MeasurableSingletonClass (Option J) := ⟨fun _ => trivial⟩
  let ν := (roundLaw s hs ht).toMeasure
  let μ := Measure.pi (fun _ : P => ν)
  let X (j : J) (q : V) (p : P) (ω : P → Option J) := if ω p = some j then a p q else 0
  let bad (z : J × V) := {ω | ε < |(∑ p, X z.1 z.2 p ω) - s z.1 * ∑ p, a p z.2|}
  have hb (z : J × V) : μ.real (bad z) ≤ 2 * Real.exp (-ε^2 / (2 * (Fintype.card P * (‖b‖/2)^2))) := by
    let g (p : P) (t : Option J) := if t = some z.1 then a p z.2 else 0
    have hg (p : P) : Measurable (g p) := measurable_of_finite _
    have hind : iIndepFun (X z.1 z.2) μ := iIndepFun_pi (μ := fun _ : P => ν)
      (X := g) (fun p => (hg p).aemeasurable)
    have hm (p : P) : Measurable (X z.1 z.2 p) := (hg p).comp (measurable_pi_apply p)
    have hx (p : P) (ω : P → Option J) : X z.1 z.2 p ω ∈ Set.Icc 0 b := by
      dsimp [X]; split_ifs
      · exact ha p z.2
      · exact ⟨le_rfl, (ha p z.2).1.trans (ha p z.2).2⟩
    have h := abs_tail μ univ hind (fun p _ => (hm p).aemeasurable)
      (fun p _ => Filter.Eventually.of_forall (hx p)) he
    have hmean (p : P) : (∫ ω, X z.1 z.2 p ω ∂μ) = s z.1 * a p z.2 :=
      coordinate_mean s hs ht z.1 p _
    simpa only [sum_sub_distrib, hmean, ← mul_sum, card_univ, bad] using h
  obtain ⟨ω, hω⟩ := exists_good_sample μ univ bad _ (fun z _ => hb z) (by simpa using hsmall)
  exact ⟨ω, fun j q => le_of_not_gt (hω (j,q) (mem_univ _))⟩

end GreenPartition
namespace GreenPartition
open Real

theorem round_budget {x n v m : ℝ} (hx : 2 < x) (hn : 0 < n) (hnx : n ≤ x)
    (hv : 0 ≤ v) (hvb : v ≤ x^2) (hm : 0 ≤ m) (hmx : m ≤ x)
    (hu : 1 ≤ log (log x))
    (hg : 4 * log x * (log (log x))^4 ≤ x^(1/5 : ℝ)) :
    m*v*(2*exp (-(1/(log (log x))^2)^2 /
      (2*(n*(‖x^(-3/5:ℝ)‖/2)^2)))) < 1 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hu0 : 0 < log (log x) := by linarith
  have hpow : 0 < x^(-3/5 : ℝ) := rpow_pos_of_pos hx0 _
  rw [Real.norm_eq_abs, abs_of_pos hpow]
  have hid : x * (x^(-3/5:ℝ))^2 * x^(1/5:ℝ) = 1 := by
    rw [← Real.rpow_mul_natCast hx0.le]
    calc
      _ = (x^((1:ℝ)+(-3/5:ℝ)*(2:ℕ)))*x^(1/5:ℝ) := by
        rw [Real.rpow_add hx0, Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have hd : 0 < 2*(n*(x^(-3/5:ℝ)/2)^2) := by positivity
  have hexp : -(1/(log (log x))^2)^2 / (2*(n*(x^(-3/5:ℝ)/2)^2)) ≤ -4 * log x := by
    apply (div_le_iff₀ hd).2
    have hprod := mul_le_mul_of_nonneg_left hg (show 0 ≤ x*(x^(-3/5:ℝ))^2 by positivity)
    have hnx' : n * (x^(-3/5:ℝ))^2 ≤ x*(x^(-3/5:ℝ))^2 := by gcongr
    have hmul := mul_le_mul_of_nonneg_right hnx' (show 0 ≤ 4*log x*(log (log x))^4 by positivity)
    field_simp
    nlinarith
  have hExp : exp (-4 * log x) = (x^4)⁻¹ := by
    rw [show (-4:ℝ)*log x = -(4*log x) by ring, exp_neg, mul_comm, ← rpow_def_of_pos hx0]
    norm_cast
  have hmv : m*v ≤ x^3 := by calc
    _ ≤ x*x^2 := mul_le_mul hmx hvb hv hx0.le
    _ = _ := by ring
  calc
    _ ≤ x^3*(2*exp (-4*log x)) := by gcongr
    _ < _ := by rw [hExp]; field_simp; nlinarith [pow_pos hx0 3, mul_pos (sub_pos.mpr hx) (pow_pos hx0 3)]
end GreenPartition

open Finset Real Filter GreenPartition

theorem OMA.solution : OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H2_R1.H2 := by
  classical
  intro K hK
  filter_upwards [eventually_round_margin, eventually_gt_atTop 2] with x hg hx
  dsimp only
  intro P V E w C m s hPx hC hCK hsize hw hprob hdegree hm hs ht
  let J := Icc 1 m
  let a (p q : ℕ) := ∑ e ∈ (E p).filter (q ∈ ·), w p e
  have hx' : (2:ℝ) < x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have hu := hg.1
  have hlog : 0 < log (x:ℝ) := log_pos (by linarith)
  have hu' : log (log (x:ℝ)) ≤ x :=
    by linarith [log_le_sub_one_of_pos hlog, log_le_sub_one_of_pos hx0]
  have hdeg (q) (hq : q ∈ V) : 1 ≤ ∑ p ∈ P, a p q := by
    have hd := (abs_le.mp (hdegree q hq)).1
    have h1 : 1 / (log (log (x:ℝ)))^2 ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    dsimp [a]; linarith
  have hv := vertex_bound P V E w _ hsize hw hdeg
  have hPx' : (P.card : ℝ) ≤ x := by exact_mod_cast hPx
  have hsqrt : √(log (x:ℝ)) ≤ x := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hx0.le, by nlinarith [log_le_sub_one_of_pos hx0]⟩
  have hv' : (V.card:ℝ) ≤ (x:ℝ)^2 :=
    hv.trans (by rw [sq]; exact mul_le_mul hPx' hsqrt (sqrt_nonneg _) hx0.le)
  by_cases hP : P.Nonempty
  · have hn : (0:ℝ) < P.card := by exact_mod_cast hP.card_pos
    have hmJ : J.card = m := by simp [J, Nat.card_Icc]
    have hJsum : ∑ j : ↥J, s j ≤ 1 := by rw [Finset.sum_coe_sort]; exact ht
    have hsmall := round_budget hx' hn hPx' (Nat.cast_nonneg _) hv' (Nat.cast_nonneg m) (hm.trans hu') hu hg.2
    obtain ⟨f, hf⟩ := finite_round (P := ↥P) (J := ↥J) (V := ↥V)
      (fun p q => a p q) (fun j => s j) (b := (x:ℝ)^(-3/5:ℝ)) (ε := 1/(log (log (x:ℝ)))^2)
      (fun p q => ⟨sum_nonneg (fun e he => (hw p p.property).2 e (mem_filter.mp he).1), hprob p p.property q q.property⟩)
      (fun j => hs j) hJsum (by positivity) (by simpa [Fintype.card_prod, hmJ] using hsmall)
    let I (j : ℕ) := P.filter (fun p => ∃ hp : p ∈ P, ∃ hj : j ∈ J, f ⟨p,hp⟩ = some ⟨j,hj⟩)
    refine ⟨I, fun j _ => filter_subset _ _, ?_, ?_⟩
    · intro j hj k hk hjk
      apply disjoint_left.mpr
      intro p hp hp'
      obtain ⟨_, h₁, h₂, he⟩ := mem_filter.mp hp
      obtain ⟨_, h₃, h₄, he'⟩ := mem_filter.mp hp'
      exact hjk (congrArg Subtype.val (Option.some.inj (he.symm.trans he')))
    · intro j hj q hq
      let jj : ↥J := ⟨j,hj⟩
      have hi (p : ↥P) : (p.val ∈ I j) ↔ f p = some jj := by
        constructor
        · intro h
          obtain ⟨_, _, _, he⟩ := mem_filter.mp h
          exact he
        · intro h
          exact mem_filter.mpr ⟨p.property, p.property, hj, h⟩
      have hsum : ∑ p ∈ I j, a p q = ∑ p : ↥P, if f p = some jj then a p q else 0 := by
        simp_rw [← hi]
        rw [Finset.sum_coe_sort P (fun t => if t ∈ I j then a t q else 0), ← sum_filter]
        congr 1
        ext p
        exact ⟨fun hp => mem_filter.mpr ⟨(mem_filter.mp hp).1, hp⟩, fun hp => (mem_filter.mp hp).2⟩
      change |(∑ p ∈ I j, a p q) - s j * ∑ p ∈ P, a p q| ≤ _
      rw [hsum, ← Finset.sum_coe_sort P (fun p => a p q)]
      exact hf jj ⟨q,hq⟩
  · have hem := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    refine ⟨fun _ => ∅, by simp, by simp, ?_⟩
    intro j hj q hq
    simp [sq_nonneg]
