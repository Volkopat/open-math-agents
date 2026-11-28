import OMAStatements.S_mo_142880
import Mathlib

/-!
The two maximizing locations have upper and lower signed tails of order
exp(-d²x/2)/(1+x)^(3/2). We first prove the Gaussian walk estimates,
then use reflection and independent increments for the continuous path.
The tail comparison gives an additive shift with multiplier one.
-/

namespace GaussianWalkSurvival

open Real Finset

private lemma inv_sqrt_step (n : ℕ) :
    (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  have h₁ : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [← one_div, div_le_iff₀ h₁]
  have h₂ := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have h₃ := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))]

lemma sum_inv_sqrt_le (n : ℕ) :
    (∑ k ∈ range n, (Real.sqrt ((k : ℝ) + 1))⁻¹) ≤ 2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_succ]
    linarith [inv_sqrt_step n]

lemma survival_upper {a : ℕ → ℝ}
    (hpos : ∀ n, 0 ≤ a n) (hmono : Antitone a)
    (hconv : ∀ n, (∑ k ∈ range (n + 1), a k * a (n - k)) = 1) (n : ℕ) :
    a n ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ := by
  have hsum : ((n : ℝ) + 1) * a n ^ 2 ≤ 1 := calc
    _ = ∑ _k ∈ range (n + 1), a n ^ 2 := by simp
    _ ≤ ∑ k ∈ range (n + 1), a k * a (n - k) := by
      refine sum_le_sum fun k hk => ?_
      rw [sq]
      exact mul_le_mul (hmono (by simpa using mem_range.mp hk))
        (hmono (Nat.sub_le ..)) (hpos n) (hpos k)
    _ = _ := hconv n
  have hroot : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hsquare : (a n * Real.sqrt ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), mul_comm]
    exact hsum
  rw [← one_div, le_div_iff₀ hroot]
  nlinarith [sq_nonneg (a n * Real.sqrt ((n : ℝ) + 1) - 1)]

lemma survival_lower {a : ℕ → ℝ}
    (hpos : ∀ n, 0 ≤ a n) (hmono : Antitone a)
    (hconv : ∀ n, (∑ k ∈ range (n + 1), a k * a (n - k)) = 1) (n : ℕ) :
    (6 * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ a n := by
  have hbound (k : ℕ) : a k * a (2 * n - k) ≤ a n * (a k + a (2 * n - k)) := by
    rcases le_or_gt n k with h | h
    · exact (mul_le_mul_of_nonneg_right (hmono h) (hpos _)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hpos _)) (hpos _))
    · rw [mul_comm (a k)]
      exact (mul_le_mul_of_nonneg_right (hmono (by omega)) (hpos _)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hpos _)) (hpos _))
  have hsum : 1 ≤ 2 * a n * (∑ k ∈ range (2 * n + 1), a k) := calc
    1 = ∑ k ∈ range (2 * n + 1), a k * a (2 * n - k) := (hconv _).symm
    _ ≤ ∑ k ∈ range (2 * n + 1), a n * (a k + a (2 * n - k)) :=
      sum_le_sum fun k _ => hbound k
    _ = _ := by
      have hreflect := sum_range_reflect a (2 * n + 1)
      simp at hreflect
      rw [← mul_sum, sum_add_distrib, hreflect]
      ring
  have hsum' : (∑ k ∈ range (2 * n + 1), a k) ≤ 2 * Real.sqrt ((2 * n + 1 : ℕ) : ℝ) :=
    (sum_le_sum fun k _ => survival_upper hpos hmono hconv k).trans (sum_inv_sqrt_le _)
  have hroot : Real.sqrt ((2 * n + 1 : ℕ) : ℝ) ≤ (3 / 2) * Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.sqrt_le_iff]
    · constructor
      · positivity
      · rw [mul_pow, Real.sq_sqrt (by positivity)]
        push_cast
        linarith
  have hh : 1 ≤ 2 * a n * (2 * ((3 / 2) * Real.sqrt ((n : ℝ) + 1))) :=
    hsum.trans (mul_le_mul_of_nonneg_left
      (hsum'.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))) (by nlinarith [hpos n]))
  rw [← one_div, div_le_iff₀ (by positivity : 0 < 6 * Real.sqrt ((n : ℝ) + 1))]
  nlinarith only [hh]

end GaussianWalkSurvival


namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Reverse the increments up to a fixed time and retain the subsequent increments. -/
noncomputable def reversePrefix (B : ℝ≥0 → Ω → ℝ) (k t : ℝ≥0) (ω : Ω) : ℝ :=
  B (max k t) ω - B (k - t) ω

lemma preBrownian_reversePrefix (hB : IsPreBrownianReal B P) (k : ℝ≥0) :
    IsPreBrownianReal (reversePrefix B k) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ ?_ ?_
  · apply hB.isGaussianProcess.of_isGaussianProcess
    intro t
    exact ⟨{max k t, k - t},
      { toFun v := v ⟨max k t, by simp⟩ - v ⟨k - t, by simp⟩
        map_add' x y := by simp; abel
        map_smul' c x := by simp; ring }, fun _ => rfl⟩
  · intro t
    unfold reversePrefix
    rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact hB.integrable_eval _
  · intro s t hst
    unfold reversePrefix
    rw [covariance_fun_sub_fun_sub]
    · simp_rw [hB.covariance_fun_eval]
      have hms : max k s ≤ max k t := max_le_max_left _ hst
      have hsubT : k - t ≤ max k s := (tsub_le_self).trans (le_max_left _ _)
      have hsubS : k - s ≤ max k t := (tsub_le_self).trans (le_max_left _ _)
      have hsub : k - t ≤ k - s := tsub_le_tsub_left hst _
      rw [min_eq_left hms, min_eq_right hsubT, min_eq_left hsubS, min_eq_right hsub]
      rcases le_or_gt s k with hsk | hsk
      · rw [max_eq_left hsk, NNReal.coe_sub hsk]
        ring
      · rw [max_eq_right hsk.le, tsub_eq_zero_of_le hsk.le]
        simp
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

def survives (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (barrier : ℝ) : Set Ω :=
  {ω | ∀ j : Fin (n + 1), -barrier ≤ B (j.val : ℝ≥0) ω}

lemma survives_prob_eq {C : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P) (n : ℕ) (barrier : ℝ) :
    P (survives B n barrier) = P (survives C n barrier) := by
  let I : Finset ℝ≥0 := (Finset.range (n + 1)).image (fun j : ℕ => (j : ℝ≥0))
  have hI (j : Fin (n + 1)) : (j.val : ℝ≥0) ∈ I :=
    Finset.mem_image.mpr ⟨j.val, Finset.mem_range.mpr j.isLt, rfl⟩
  let A : Set (I → ℝ) := {x | ∀ j : Fin (n + 1), -barrier ≤ x ⟨j.val, hI j⟩}
  have hA : MeasurableSet A := by
    have hset : A = ⋂ j : Fin (n + 1), {x : I → ℝ | -barrier ≤ x ⟨j.val, hI j⟩} := by
      ext x
      simp [A]
    rw [hset]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply _)
  calc
    P (survives B n barrier) = BrownianReal.projectiveFamily I A := (hB.hasLaw I).measure_eq hA
    _ = P (survives C n barrier) := ((hC.hasLaw I).measure_eq hA).symm

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

noncomputable def survivalProbability (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (n : ℕ) (y : ℝ) : ℝ :=
  P.real (survives B n y)

lemma survivalProbability_nonneg (n : ℕ) (y : ℝ) :
    0 ≤ survivalProbability B P n y := ENNReal.toReal_nonneg

lemma survivalProbability_antitone (y : ℝ) : Antitone (fun n => survivalProbability B P n y) := by
  intro m n h
  apply measureReal_mono _ (measure_ne_top P _)
  intro ω hω j
  exact hω ⟨j.val, by omega⟩

def maximumAt (B : ℝ≥0 → Ω → ℝ) {n : ℕ} (k : Fin (n + 1)) : Set Ω :=
  {ω | ∀ j : Fin (n + 1), B (j.val : ℝ≥0) ω ≤ B (k.val : ℝ≥0) ω}

lemma maximumAt_nullMeasurable (hB : IsPreBrownianReal B P) {n : ℕ} (k : Fin (n + 1)) :
    NullMeasurableSet (maximumAt B k) P := by
  rw [show maximumAt B k =
    ⋂ j : Fin (n + 1), {ω | B (j.val : ℝ≥0) ω ≤ B (k.val : ℝ≥0) ω} by ext ω; simp [maximumAt]]
  exact NullMeasurableSet.iInter fun j => nullMeasurableSet_le (hB.aemeasurable _) (hB.aemeasurable _)

lemma measure_eq_eval_zero (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≠ t) :
    P {ω | B s ω = B t ω} = 0 := by
  have hv : nndist (s : ℝ) (t : ℝ) ≠ 0 := by
    intro h
    exact hst (NNReal.eq (nndist_eq_zero.mp h))
  letI : NullSingletonClass (gaussianReal 0 (nndist (s : ℝ) (t : ℝ))) :=
    nullSingletonClass_gaussianReal hv
  have hz : gaussianReal 0 (nndist (s : ℝ) (t : ℝ)) {0} = 0 := measure_singleton 0
  have hm := (hB.hasLaw_sub s t).measure_eq (p := fun x : ℝ => x = 0) (measurableSet_singleton 0)
  have hset : {ω | B s ω = B t ω} = {ω | (B s - B t) ω = 0} := by
    ext ω
    simp [Pi.sub_apply, sub_eq_zero]
  rw [hset, hm]
  exact hz

private def shiftAfter (B : ℝ≥0 → Ω → ℝ) (k t : ℝ≥0) (ω : Ω) : ℝ :=
  B (k + t) ω - B k ω

private def pastProjection (B : ℝ≥0 → Ω → ℝ) (k : ℝ≥0) (ω : Ω) (t : Set.Iic k) : ℝ :=
  B t.val ω

private def pastCyl (k : ℕ) : Set (Set.Iic (k : ℝ≥0) → ℝ) :=
  {f | ∀ j : Fin (k + 1),
    f ⟨(k : ℝ≥0) - (j.val : ℝ≥0), mem_Iic.mpr tsub_le_self⟩ ≤ f ⟨k, mem_Iic.mpr le_rfl⟩}

private def futureCyl (m : ℕ) : Set (ℝ≥0 → ℝ) :=
  {f | ∀ j : Fin (m + 1), f (j.val : ℝ≥0) ≤ 0}

private lemma pastCyl_meas (k : ℕ) : MeasurableSet (pastCyl k) := by
  rw [show pastCyl k = ⋂ j : Fin (k + 1), {f : Set.Iic (k : ℝ≥0) → ℝ |
      f ⟨(k : ℝ≥0) - (j.val : ℝ≥0), mem_Iic.mpr tsub_le_self⟩ ≤ f ⟨k, mem_Iic.mpr le_rfl⟩} by
      ext f; simp [pastCyl]]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)

private lemma futureCyl_meas (m : ℕ) : MeasurableSet (futureCyl m) := by
  rw [show futureCyl m = ⋂ j : Fin (m + 1), {f : ℝ≥0 → ℝ | f (j.val : ℝ≥0) ≤ 0} by
      ext f; simp [futureCyl]]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply _) measurable_const

private lemma pastCyl_preimage (B : ℝ≥0 → Ω → ℝ) (k : ℕ) :
    pastProjection B k ⁻¹' pastCyl k = survives (reversePrefix B k) k 0 := by
  ext ω
  change (∀ j : Fin (k + 1), B ((k : ℝ≥0) - (j.val : ℝ≥0)) ω ≤ B k ω) ↔ _
  simp only [survives, mem_ofPred_eq, neg_zero, reversePrefix, sub_nonneg]
  apply forall_congr'
  intro j
  have hj : (j.val : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast (show j.val ≤ k by omega)
  rw [max_eq_left hj]

private lemma futureCyl_preimage (B : ℝ≥0 → Ω → ℝ) (k m : ℕ) :
    (fun ω t => shiftAfter B k t ω) ⁻¹' futureCyl m = survives (-(shiftAfter B k)) m 0 := by
  ext ω
  change (∀ j : Fin (m + 1), shiftAfter B (k : ℝ≥0) (j.val : ℝ≥0) ω ≤ 0) ↔ _
  simp [survives]

private lemma cast_sub_index {i k : ℕ} (h : i ≤ k) :
    (k : ℝ≥0) - ((k - i : ℕ) : ℝ≥0) = (i : ℝ≥0) := by
  have hs : (i : ℝ≥0) + ((k - i : ℕ) : ℝ≥0) = k := by
    exact_mod_cast (Nat.add_sub_of_le h)
  rw [← hs, add_tsub_cancel_right]

private lemma maximumAt_decompose (B : ℝ≥0 → Ω → ℝ) {n : ℕ} (k : Fin (n + 1)) :
    maximumAt B k =
      (pastProjection B k.val ⁻¹' pastCyl k.val) ∩
      ((fun ω t => shiftAfter B k.val t ω) ⁻¹' futureCyl (n - k.val)) := by
  ext ω
  change (∀ j : Fin (n + 1), B (j.val : ℝ≥0) ω ≤ B (k.val : ℝ≥0) ω) ↔
    (∀ j : Fin (k.val + 1), B ((k.val : ℝ≥0) - (j.val : ℝ≥0)) ω ≤ B (k.val : ℝ≥0) ω) ∧
      (∀ j : Fin (n - k.val + 1), B ((k.val : ℝ≥0) + (j.val : ℝ≥0)) ω - B (k.val : ℝ≥0) ω ≤ 0)
  constructor
  · intro h
    constructor
    · intro j
      let i : Fin (n + 1) := ⟨k.val - j.val, by omega⟩
      have hcast : ((i.val : ℕ) : ℝ≥0) = (k.val : ℝ≥0) - (j.val : ℝ≥0) := by
        apply NNReal.eq
        push_cast [NNReal.coe_sub (show (j.val : ℝ≥0) ≤ (k.val : ℝ≥0) by exact_mod_cast (show j.val ≤ k.val by omega))]
        exact Nat.cast_sub (by omega)
      simpa only [hcast] using h i
    · intro j
      let i : Fin (n + 1) := ⟨k.val + j.val, by omega⟩
      exact sub_nonpos.mpr (by simpa only [i, Nat.cast_add] using h i)
  · rintro ⟨hp, hf⟩ j
    rcases le_or_gt j.val k.val with hj | hj
    · let i : Fin (k.val + 1) := ⟨k.val - j.val, by omega⟩
      simpa only [i, cast_sub_index hj] using hp i
    · let i : Fin (n - k.val + 1) := ⟨j.val - k.val, by omega⟩
      have hi : (k.val : ℝ≥0) + (i.val : ℝ≥0) = (j.val : ℝ≥0) := by
        exact_mod_cast (Nat.add_sub_of_le hj.le)
      simpa only [hi] using sub_nonpos.mp (hf i)

lemma maximumAt_measure (hB : IsPreBrownianReal B P) {n : ℕ} (k : Fin (n + 1)) :
    P (maximumAt B k) = P (survives B k.val 0) * P (survives B (n - k.val) 0) := by
  have hi : IndepFun (pastProjection B (k.val : ℝ≥0)) (fun ω t => shiftAfter B k.val t ω) P :=
    (hB.indepFun_shift (k.val : ℝ≥0)).symm
  have hC : IsPreBrownianReal (-(shiftAfter B (k.val : ℝ≥0))) P :=
    IsPreBrownianReal.neg (hB.shift (k.val : ℝ≥0))
  rw [maximumAt_decompose, hi.measure_inter_preimage_eq_mul _ _ (pastCyl_meas _) (futureCyl_meas _)]
  rw [pastCyl_preimage, futureCyl_preimage,
    survives_prob_eq (preBrownian_reversePrefix hB (k.val : ℝ≥0)) hB,
    survives_prob_eq hC hB]

lemma survivalProbability_convolution (hB : IsPreBrownianReal B P) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      survivalProbability B P k 0 * survivalProbability B P (n - k) 0 = 1 := by
  classical
  have hdisj : Pairwise (fun i j : Fin (n + 1) => AEDisjoint P (maximumAt B i) (maximumAt B j)) := by
    intro i j hij
    apply measure_mono_null ?_ (measure_eq_eval_zero hB (s := (i.val : ℝ≥0)) (t := (j.val : ℝ≥0))
      (by
        intro h
        apply hij
        apply Fin.ext
        exact_mod_cast h))
    intro ω hω
    exact le_antisymm (hω.2 i) (hω.1 j)
  have hunion : ⋃ k : Fin (n + 1), maximumAt B k = univ := by
    ext ω
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
      (fun k : Fin (n + 1) => B (k.val : ℝ≥0) ω) Finset.univ_nonempty
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨k, fun j => hk j (Finset.mem_univ _)⟩
  have hsum : ∑ k : Fin (n + 1), P (maximumAt B k) = 1 := by
    simpa only [tsum_fintype, hunion, measure_univ] using
      (measure_iUnion₀ hdisj (maximumAt_nullMeasurable hB)).symm
  have hsumR := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun k _ => measure_ne_top P _), ENNReal.toReal_one] at hsumR
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [maximumAt_measure hB, ENNReal.toReal_mul, survivalProbability, measureReal_def] using hsumR

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

private lemma upperFiberCorrelation {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (A : Set (U × ℝ)) (hA : MeasurableSet A)
    (hmono : ∀ u, IsUpperSet (Prod.mk u ⁻¹' A)) (y : ℝ) :
    (μ.prod ν) A * ν (Ici y) ≤ (μ.prod ν) (A ∩ (univ ×ˢ Ici y)) := by
  rw [Measure.prod_apply hA, Measure.prod_apply (hA.inter (MeasurableSet.univ.prod measurableSet_Ici)),
    ← lintegral_mul_const' _ _ (measure_ne_top ν (Ici y))]
  apply lintegral_mono
  intro u
  have hfib : Prod.mk u ⁻¹' (A ∩ (univ ×ˢ Ici y)) = (Prod.mk u ⁻¹' A) ∩ Ici y := by
    ext z
    simp
  change ν (Prod.mk u ⁻¹' A) * ν (Ici y) ≤ ν (Prod.mk u ⁻¹' (A ∩ (univ ×ˢ Ici y)))
  rw [hfib]
  by_cases h : Prod.mk u ⁻¹' A ⊆ Ici y
  · rw [inter_eq_left.mpr h]
    calc
      _ ≤ ν (Prod.mk u ⁻¹' A) * 1 := by gcongr; exact prob_le_one
      _ = _ := mul_one _
  · have hsub : Ici y ⊆ Prod.mk u ⁻¹' A := by
      obtain ⟨z, hz, hzy⟩ := Set.not_subset.mp h
      exact fun t ht => hmono u (le_trans (lt_of_not_ge hzy).le ht) hz
    rw [inter_eq_right.mpr hsub]
    calc
      _ ≤ 1 * ν (Ici y) := by gcongr; exact prob_le_one
      _ = _ := one_mul _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

private noncomputable def gridFraction {m : ℕ} (j : Fin (m + 1)) : ℝ := (j.val : ℝ) / m

private noncomputable def walkBridge (B : ℝ≥0 → Ω → ℝ) {m : ℕ} (j : Fin (m + 1)) (ω : Ω) : ℝ :=
  B (j.val : ℝ≥0) ω - gridFraction j * B (m : ℝ≥0) ω

private lemma aemeasurable_walkBridge (hB : IsPreBrownianReal B P) {m : ℕ} (j : Fin (m + 1)) :
    AEMeasurable (walkBridge B j) P :=
  (hB.aemeasurable _).sub (aemeasurable_const.mul (hB.aemeasurable _))

private lemma indepFun_walkBridge_endpoint (hB : IsPreBrownianReal B P) {m : ℕ} (hm : 0 < m) :
    IndepFun (fun ω (j : Fin (m + 1)) => walkBridge B j ω) (B (m : ℝ≥0)) P := by
  let Y : Unit → Ω → ℝ := fun _ => B (m : ℝ≥0)
  have hJoint : IsGaussianProcess (Sum.elim (walkBridge B (m := m)) Y) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    intro i
    cases i with
    | inl j =>
      refine ⟨{(j.val : ℝ≥0), (m : ℝ≥0)},
        { toFun v := v ⟨j.val, by simp⟩ - gridFraction j * v ⟨m, by simp⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }, fun _ => rfl⟩
    | inr t =>
      exact ⟨{(m : ℝ≥0)},
        { toFun v := v ⟨m, by simp⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }, fun _ => rfl⟩
  have hIndep := hJoint.indepFun_of_covariance_eq_zero (aemeasurable_walkBridge hB)
    (fun _ => hB.aemeasurable _) (fun j _ => by
      have hj : (j.val : ℝ≥0) ≤ (m : ℝ≥0) := by exact_mod_cast (show j.val ≤ m by omega)
      have hpos : (0 : ℝ) < m := by exact_mod_cast hm
      change cov[fun ω => B (j.val : ℝ≥0) ω - gridFraction j * B (m : ℝ≥0) ω,
        B (m : ℝ≥0); P] = 0
      rw [covariance_fun_sub_left, covariance_const_mul_left, hB.covariance_eval,
        hB.covariance_eval, min_eq_left hj, min_self]
      · simp only [NNReal.coe_natCast, gridFraction]
        field_simp
        <;> ring
      all_goals
        first
        | exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
        | exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _)
  exact hIndep.comp measurable_id (measurable_pi_apply ())

lemma survival_endpoint_correlation (hB : IsPreBrownianReal B P) {m : ℕ} (hm : 0 < m) (y : ℝ) :
    P (survives B m 0) * P {ω | y ≤ B (m : ℝ≥0) ω} ≤
      P (survives B m 0 ∩ {ω | y ≤ B (m : ℝ≥0) ω}) := by
  let V (ω : Ω) (j : Fin (m + 1)) := walkBridge B j ω
  let X := B (m : ℝ≥0)
  let A : Set ((Fin (m + 1) → ℝ) × ℝ) :=
    {z | ∀ j : Fin (m + 1), 0 ≤ z.1 j + gridFraction j * z.2}
  have hV : AEMeasurable V P := aemeasurable_pi_lambda _ (aemeasurable_walkBridge hB)
  have hX : AEMeasurable X P := hB.aemeasurable _
  letI : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hV
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  have hMeas : MeasurableSet A := by
    rw [show A = ⋂ j : Fin (m + 1), {z : (Fin (m + 1) → ℝ) × ℝ |
      0 ≤ z.1 j + gridFraction j * z.2} by ext z; simp [A]]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const
      (((measurable_pi_apply j).comp measurable_fst).add (measurable_const.mul measurable_snd))
  have hMono (v : Fin (m + 1) → ℝ) : IsUpperSet (Prod.mk v ⁻¹' A) := by
    intro x t hxt hx j
    have hnonneg : 0 ≤ gridFraction j := by unfold gridFraction; positivity
    exact le_trans (hx j) (add_le_add_right (mul_le_mul_of_nonneg_left hxt hnonneg) _)
  have hMap : P.map (fun ω => (V ω, X ω)) = (P.map V).prod (P.map X) :=
    (indepFun_walkBridge_endpoint hB hm).map_prod_eq_prod_map_map hV hX
  have hPre : (fun ω => (V ω, X ω)) ⁻¹' A = survives B m 0 := by
    ext ω
    simp [A, V, X, survives, walkBridge]
  have hA : ((P.map V).prod (P.map X)) A = P (survives B m 0) := by
    rw [← hMap, Measure.map_apply_of_aemeasurable (hV.prodMk hX) hMeas, hPre]
  have hI : ((P.map V).prod (P.map X)) (A ∩ (univ ×ˢ Ici y)) =
      P (survives B m 0 ∩ {ω | y ≤ B (m : ℝ≥0) ω}) := by
    rw [← hMap, Measure.map_apply_of_aemeasurable (hV.prodMk hX)
      (hMeas.inter (MeasurableSet.univ.prod measurableSet_Ici)), preimage_inter, hPre]
    congr 1
    ext ω
    simp [X]
  have hTail : P.map X (Ici y) = P {ω | y ≤ B (m : ℝ≥0) ω} :=
    Measure.map_apply_of_aemeasurable hX measurableSet_Ici
  simpa only [hA, hI, hTail] using upperFiberCorrelation (P.map V) (P.map X) A hMeas hMono y

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

private def walkGridIndex {n : ℕ} (i : Fin (n + 1)) : Set.Iic (n : ℝ≥0) :=
  ⟨(i.val : ℝ≥0), mem_Iic.mpr (by exact_mod_cast (show i.val ≤ n by omega))⟩

private def seedCyl (m : ℕ) (y : ℝ) : Set (Set.Iic (m : ℝ≥0) → ℝ) :=
  {f | (∀ j : Fin (m + 1), 0 ≤ f (walkGridIndex j)) ∧ y ≤ f ⟨m, mem_Iic.mpr le_rfl⟩}

private def barrierCyl (n : ℕ) (y : ℝ) : Set (ℝ≥0 → ℝ) :=
  {f | ∀ j : Fin (n + 1), -y ≤ f (j.val : ℝ≥0)}

private lemma seedCyl_meas (m : ℕ) (y : ℝ) : MeasurableSet (seedCyl m y) := by
  rw [show seedCyl m y =
    (⋂ j : Fin (m + 1), {f : Set.Iic (m : ℝ≥0) → ℝ | 0 ≤ f (walkGridIndex j)}) ∩
      {f : Set.Iic (m : ℝ≥0) → ℝ | y ≤ f ⟨m, mem_Iic.mpr le_rfl⟩} by ext f; simp [seedCyl]]
  exact (MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply _)).inter
    (measurableSet_le measurable_const (measurable_pi_apply _))

private lemma barrierCyl_meas (n : ℕ) (y : ℝ) : MeasurableSet (barrierCyl n y) := by
  rw [show barrierCyl n y = ⋂ j : Fin (n + 1), {f : ℝ≥0 → ℝ | -y ≤ f (j.val : ℝ≥0)} by
    ext f; simp [barrierCyl]]
  exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply _)

lemma survival_seed_extend (hB : IsPreBrownianReal B P) {m : ℕ} (hm : 0 < m) (n : ℕ) (y : ℝ) :
    P (survives B m 0) * P {ω | y ≤ B (m : ℝ≥0) ω} * P (survives B n y) ≤
      P (survives B (m + n) 0) := by
  let F := pastProjection B (m : ℝ≥0)
  let G (ω : Ω) (t : ℝ≥0) := shiftAfter B (m : ℝ≥0) t ω
  have hi : IndepFun F G P := (hB.indepFun_shift (m : ℝ≥0)).symm
  have hP : F ⁻¹' seedCyl m y = survives B m 0 ∩ {ω | y ≤ B (m : ℝ≥0) ω} := by
    ext ω
    simp [F, pastProjection, seedCyl, survives, walkGridIndex]
  have hG : G ⁻¹' barrierCyl n y = survives (shiftAfter B (m : ℝ≥0)) n y := rfl
  have hC : IsPreBrownianReal (shiftAfter B (m : ℝ≥0)) P := hB.shift (m : ℝ≥0)
  have hlen : P (G ⁻¹' barrierCyl n y) = P (survives B n y) := by
    rw [hG, survives_prob_eq hC hB]
  calc
    _ ≤ P (F ⁻¹' seedCyl m y) * P (G ⁻¹' barrierCyl n y) := by
      rw [hP, hlen]
      gcongr
      exact survival_endpoint_correlation hB hm y
    _ = P (F ⁻¹' seedCyl m y ∩ G ⁻¹' barrierCyl n y) :=
      (hi.measure_inter_preimage_eq_mul _ _ (seedCyl_meas m y) (barrierCyl_meas n y)).symm
    _ ≤ _ := by
      apply measure_mono
      rw [hP, hG]
      intro ω hω j
      change -(0 : ℝ) ≤ B (j.val : ℝ≥0) ω
      simp only [neg_zero]
      rcases le_or_gt j.val m with hj | hj
      · simpa only [neg_zero] using hω.1.1 ⟨j.val, by omega⟩
      · let i : Fin (n + 1) := ⟨j.val - m, by omega⟩
        have hcast : (m : ℝ≥0) + (i.val : ℝ≥0) = (j.val : ℝ≥0) := by
          exact_mod_cast (Nat.add_sub_of_le hj.le)
        have h := hω.2 i
        change -y ≤ B ((m : ℝ≥0) + (i.val : ℝ≥0)) ω - B (m : ℝ≥0) ω at h
        rw [hcast] at h
        have he : y ≤ B (m : ℝ≥0) ω := hω.1.2
        linarith

private noncomputable def gaussianSeedProbability : ℝ := (gaussianReal 0 1).real (Ici 1)

lemma gaussianSeedProbability_pos : 0 < gaussianSeedProbability := by
  have hne : (gaussianReal 0 1) (Ici 1) ≠ 0 := by
    intro h
    have hvol := (gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)) h
    rw [Real.volume_Ici] at hvol
    exact ENNReal.top_ne_zero hvol
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

lemma endpoint_atLeast_gaussianSeed (hB : IsPreBrownianReal B P) {r : ℕ} (hr : 0 < r)
    {y : ℝ} (hy : y ≤ r) :
    gaussianSeedProbability ≤ P.real {ω | y ≤ B ((r ^ 2 : ℕ) : ℝ≥0) ω} := by
  let m : ℝ≥0 := ((r ^ 2 : ℕ) : ℝ≥0)
  have hm : m ≠ 0 := by push_cast [m]; positivity
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsqrt : Real.sqrt (m : ℝ) = (r : ℝ) := by
    push_cast [m]
    exact Real.sqrt_sq hrR.le
  have hScale := ((hB.smul hm).hasLaw_eval 1).measureReal_eq
    (p := fun x : ℝ => (1 : ℝ) ≤ x) measurableSet_Ici
  calc
    gaussianSeedProbability =
        P.real {ω | (1 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ * B (m * 1) ω} := hScale.symm
    _ ≤ _ := by
      apply measureReal_mono _ (measure_ne_top P _)
      intro ω hω
      change (1 : ℝ) ≤ (Real.sqrt (m : ℝ))⁻¹ * B (m * 1) ω at hω
      rw [mul_one, hsqrt, inv_mul_eq_div, le_div_iff₀ hrR, one_mul] at hω
      exact hy.trans hω

lemma survivalProbability_zero_upper (hB : IsPreBrownianReal B P) (n : ℕ) :
    survivalProbability B P n 0 ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ :=
  survival_upper (fun m => survivalProbability_nonneg m 0) (survivalProbability_antitone 0)
    (survivalProbability_convolution hB) n

lemma survivalProbability_zero_lower (hB : IsPreBrownianReal B P) (n : ℕ) :
    (6 * Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ survivalProbability B P n 0 :=
  survival_lower (fun m => survivalProbability_nonneg m 0) (survivalProbability_antitone 0)
    (survivalProbability_convolution hB) n

theorem survivalProbability_barrier_upper (hB : IsPreBrownianReal B P) (n : ℕ)
    {y : ℝ} (hy : 0 ≤ y) :
    survivalProbability B P n y ≤ (18 / gaussianSeedProbability) * (1 + y) / Real.sqrt ((n : ℝ) + 1) := by
  let r := ⌈y⌉₊ + 1
  let m := r ^ 2
  have hr : 0 < r := by omega
  have hm : 0 < m := by unfold m; positivity
  have hyr : y ≤ r := by
    have h := Nat.le_ceil y
    push_cast [r]
    linarith
  have hry : (r : ℝ) ≤ y + 2 := by
    have h := Nat.ceil_lt_add_one hy
    push_cast [r]
    linarith
  let u := Real.sqrt ((n : ℝ) + 1)
  let v := Real.sqrt ((m : ℝ) + 1)
  have hu : 0 < u := Real.sqrt_pos.2 (by positivity)
  have hv : 0 < v := Real.sqrt_pos.2 (by positivity)
  have hvs : v ≤ 3 * (1 + y) := by
    have hvr : v ≤ (r : ℝ) + 1 := by
      change Real.sqrt ((m : ℝ) + 1) ≤ (r : ℝ) + 1
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · push_cast [m]
        nlinarith [Nat.cast_nonneg (α := ℝ) r]
    linarith
  have hsqrt : u ≤ Real.sqrt (((m + n : ℕ) : ℝ) + 1) := by
    refine Real.sqrt_le_sqrt ?_
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hs : survivalProbability B P m 0 *
      (P.real {ω | y ≤ B (m : ℝ≥0) ω}) * survivalProbability B P n y ≤
      survivalProbability B P (m + n) 0 := by
    simpa only [survivalProbability, measureReal_def, ENNReal.toReal_mul] using
      ENNReal.toReal_mono (measure_ne_top P _) (survival_seed_extend hB hm n y)
  have hlow := mul_le_mul (survivalProbability_zero_lower hB m)
    (endpoint_atLeast_gaussianSeed hB hr hyr) gaussianSeedProbability_pos.le
    (survivalProbability_nonneg (P := P) (B := B) m 0)
  have hnlo : 0 ≤ survivalProbability B P n y := survivalProbability_nonneg n y
  have hupper : survivalProbability B P (m + n) 0 ≤ u⁻¹ :=
    (survivalProbability_zero_upper hB _).trans (inv_anti₀ hu hsqrt)
  have hfrac : ((6 * v)⁻¹ * gaussianSeedProbability) * survivalProbability B P n y ≤ u⁻¹ :=
    ((mul_le_mul_of_nonneg_right hlow hnlo).trans hs).trans hupper
  have hc := gaussianSeedProbability_pos
  have hmul := mul_le_mul_of_nonneg_right hfrac (by positivity : 0 ≤ 6 * v * u)
  have hSimpl :
      ((6 * v)⁻¹ * gaussianSeedProbability * survivalProbability B P n y) * (6 * v * u) =
      survivalProbability B P n y * (gaussianSeedProbability * u) := by
    field_simp
    <;> ring
  have hSimpl' : u⁻¹ * (6 * v * u) = 6 * v := by field_simp
  rw [hSimpl, hSimpl'] at hmul
  change survivalProbability B P n y ≤ (18 / gaussianSeedProbability) * (1 + y) / u
  apply (le_div_iff₀ hu).2
  apply (mul_le_mul_iff_left₀ hc).1
  have hfinal : (18 / gaussianSeedProbability * (1 + y)) * gaussianSeedProbability = 18 * (1 + y) := by
    field_simp
  rw [hfinal]
  calc
    _ ≤ 6 * v := by linarith only [hmul]
    _ ≤ _ := by linarith only [hvs]

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

private lemma centered_pdf_le {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (Real.sqrt (v : ℝ))⁻¹ := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have harg : (v : ℝ) ≤ 2 * Real.pi * v := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hπ hvR.le
  have hroot := Real.sqrt_le_sqrt harg
  have hrootPos := Real.sqrt_pos.2 hvR
  have hExp : Real.exp (-((x - 0) ^ 2) / (2 * (v : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  unfold gaussianPDFReal
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact inv_anti₀ hrootPos hroot

/-- No interval of length one contains more Gaussian mass than its maximal density bound. -/
lemma centered_gaussian_unit_interval_le {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    (gaussianReal 0 v).real (Icc c (c + 1)) ≤ (Real.sqrt (v : ℝ))⁻¹ := by
  let I := Icc c (c + 1)
  letI : IsFiniteMeasure (volume.restrict I) := ⟨by
    simpa [I] using (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))⟩
  have hInt : Integrable (gaussianPDFReal 0 v) (volume.restrict I) :=
    (integrable_gaussianPDFReal _ _).restrict
  have hNonneg : 0 ≤ ∫ x in I, gaussianPDFReal 0 v x :=
    integral_nonneg fun x => gaussianPDFReal_nonneg 0 v x
  change ((gaussianReal 0 v) I).toReal ≤ _
  rw [gaussianReal_apply_eq_integral _ hv I, ENNReal.toReal_ofReal hNonneg]
  calc
    _ ≤ ∫ x in I, (Real.sqrt (v : ℝ))⁻¹ :=
      integral_mono hInt (integrable_const _) (centered_pdf_le hv)
    _ = _ := by
      rw [setIntegral_const]
      change (volume (Icc c (c + 1))).toReal • (Real.sqrt (v : ℝ))⁻¹ = _
      rw [Real.volume_Icc, show c + 1 - c = 1 by ring]
      simp

lemma centered_gaussian_unit_interval_measure_le {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal 0 v (Icc c (c + 1)) ≤ ENNReal.ofReal (Real.sqrt (v : ℝ))⁻¹ := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact centered_gaussian_unit_interval_le hv c

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

private lemma prod_le_of_fiber_bound (μ : Measure U) (ν : Measure V) [SFinite ν]
    {A : Set U} (hA : MeasurableSet A) {S : Set (U × V)} (hS : MeasurableSet S) (c : ℝ≥0∞)
    (h : ∀ u, ν (Prod.mk u ⁻¹' S) ≤ A.indicator (fun _ => c) u) :
    (μ.prod ν) S ≤ c * μ A := by
  rw [Measure.prod_apply hS]
  refine (lintegral_mono h).trans_eq ?_
  rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]

private def tripleWindow (A : Set U) (C : Set V) (f : U → ℝ) (g : V → ℝ) (y : ℝ) :
    Set (V × (U × ℝ)) :=
  {z | z.1 ∈ C ∧ z.2.1 ∈ A ∧ z.2.2 ∈ Icc (y - f z.2.1 - g z.1) (y - f z.2.1 - g z.1 + 1)}

private lemma tripleWindow_meas {A : Set U} {C : Set V} (hA : MeasurableSet A) (hC : MeasurableSet C)
    {f : U → ℝ} {g : V → ℝ} (hf : Measurable f) (hg : Measurable g) (y : ℝ) :
    MeasurableSet (tripleWindow A C f g y) := by
  have hμ : Measurable (fun z : V × (U × ℝ) => y - f z.2.1 - g z.1) :=
    (measurable_const.sub (hf.comp (measurable_fst.comp measurable_snd))).sub
      (hg.comp measurable_fst)
  exact (measurable_fst hC).inter (((measurable_fst.comp measurable_snd) hA).inter
    ((measurableSet_le hμ (measurable_snd.comp measurable_snd)).inter
      (measurableSet_le (measurable_snd.comp measurable_snd) (hμ.add measurable_const))))

lemma tripleWindow_le (μ : Measure U) [IsProbabilityMeasure μ] (ν : Measure V)
    (v : ℝ≥0) (hv : v ≠ 0) {A : Set U} {C : Set V} (hA : MeasurableSet A) (hC : MeasurableSet C)
    {f : U → ℝ} {g : V → ℝ} (hf : Measurable f) (hg : Measurable g) (y : ℝ) :
    (ν.prod (μ.prod (gaussianReal 0 v))) (tripleWindow A C f g y) ≤
      ENNReal.ofReal (Real.sqrt (v : ℝ))⁻¹ * μ A * ν C := by
  let δ := ENNReal.ofReal (Real.sqrt (v : ℝ))⁻¹
  apply prod_le_of_fiber_bound _ _ hC (tripleWindow_meas hA hC hf hg y) (δ * μ A)
  intro z
  by_cases hz : z ∈ C
  · simp only [indicator_of_mem hz]
    have hsection : Prod.mk z ⁻¹' tripleWindow A C f g y =
        {p : U × ℝ | p.1 ∈ A ∧ p.2 ∈ Icc (y - f p.1 - g z) (y - f p.1 - g z + 1)} := by
      ext p
      simp [tripleWindow, hz]
    rw [hsection]
    have hwindow : MeasurableSet {p : U × ℝ | p.1 ∈ A ∧
        p.2 ∈ Icc (y - f p.1 - g z) (y - f p.1 - g z + 1)} := by
      have hleft : Measurable (fun p : U × ℝ => y - f p.1 - g z) :=
        (measurable_const.sub (hf.comp measurable_fst)).sub measurable_const
      exact (measurable_fst hA).inter ((measurableSet_le hleft measurable_snd).inter
        (measurableSet_le measurable_snd (hleft.add measurable_const)))
    apply prod_le_of_fiber_bound _ _ hA hwindow δ
    intro u
    by_cases hu : u ∈ A
    · have hslice : Prod.mk u ⁻¹' {p : U × ℝ | p.1 ∈ A ∧ p.2 ∈
            Icc (y - f p.1 - g z) (y - f p.1 - g z + 1)} =
          Icc (y - f u - g z) (y - f u - g z + 1) := by ext x; simp [hu]
      rw [indicator_of_mem hu, hslice]
      exact centered_gaussian_unit_interval_measure_le hv _
    · simp [hu]
  · simp [tripleWindow, hz]

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

def centeredEndpoint (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (barrier y : ℝ) : Set Ω :=
  survives B n barrier ∩ {ω | B (n : ℝ≥0) ω ∈ Icc (y - barrier) (y - barrier + 1)}

private lemma natCast_sub_nnreal {i n : ℕ} (hi : i ≤ n) :
    ((n - i : ℕ) : ℝ≥0) = (n : ℝ≥0) - i := by
  apply NNReal.eq
  rw [NNReal.coe_sub (by exact_mod_cast hi)]
  simpa only [NNReal.coe_natCast] using (Nat.cast_sub (R := ℝ) hi)

lemma centeredEndpoint_three_blocks (hB : IsPreBrownianReal B P) (r m : ℕ) (hm : 0 < m)
    (barrier y : ℝ) :
    P.real (centeredEndpoint B (r + m + r) barrier y) ≤
      (Real.sqrt (m : ℝ))⁻¹ * survivalProbability B P r barrier * survivalProbability B P r (y + 1) := by
  let t₀ : ℝ≥0 := r
  let t₁ : ℝ≥0 := t₀ + (m : ℝ≥0)
  let t₂ : ℝ≥0 := t₁ + t₀
  have ht₁ : t₀ ≤ t₁ := by simp [t₁]
  have ht₂ : (↑(r + m + r) : ℝ≥0) = t₂ := by simp [t₂, t₁, t₀, Nat.cast_add]
  let U (ω : Ω) (j : Fin (r + 1)) := B (j.val : ℝ≥0) ω
  let X (ω : Ω) := B t₁ ω - B t₀ ω
  let Cstep := shiftAfter B t₁
  let Vproc := reversePrefix Cstep t₀
  let V (ω : Ω) (j : Fin (r + 1)) := Vproc (j.val : ℝ≥0) ω
  have hVproc : IsPreBrownianReal Vproc P := preBrownian_reversePrefix (hB.shift t₁) t₀
  have hU : AEMeasurable U P := aemeasurable_pi_lambda _ (fun _ => hB.aemeasurable _)
  have hX : AEMeasurable X P := (hB.aemeasurable t₁).sub (hB.aemeasurable t₀)
  have hV : AEMeasurable V P := aemeasurable_pi_lambda _ (fun _ => hVproc.aemeasurable _)
  let Ufirst (f : Set.Iic t₀ → ℝ) (j : Fin (r + 1)) := f (walkGridIndex j)
  have hUfirst : Measurable Ufirst := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hUX : IndepFun U X P :=
    (hB.indepFun_shift t₀).symm.comp hUfirst (measurable_pi_apply (m : ℝ≥0))
  let i₀ : Set.Iic t₁ := ⟨t₀, mem_Iic.mpr ht₁⟩
  let i₁ : Set.Iic t₁ := ⟨t₁, mem_Iic.mpr le_rfl⟩
  let before (j : Fin (r + 1)) : Set.Iic t₁ :=
    ⟨(j.val : ℝ≥0), mem_Iic.mpr (le_trans (by
      change (j.val : ℝ≥0) ≤ (r : ℝ≥0)
      exact_mod_cast (show j.val ≤ r by omega)) ht₁)⟩
  let beforePair (f : Set.Iic t₁ → ℝ) := ((fun j => f (before j)), f i₁ - f i₀)
  have hbefore : Measurable beforePair :=
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).prodMk
      ((measurable_pi_apply i₁).sub (measurable_pi_apply i₀))
  let endReversal (f : ℝ≥0 → ℝ) (j : Fin (r + 1)) :=
    f (max t₀ (j.val : ℝ≥0)) - f (t₀ - (j.val : ℝ≥0))
  have hend : Measurable endReversal :=
    measurable_pi_lambda _ (fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _))
  have hVUX : IndepFun V (fun ω => (U ω, X ω)) P :=
    (hB.indepFun_shift t₁).comp hend hbefore
  have hvar : nndist (t₁ : ℝ) (t₀ : ℝ) = (m : ℝ≥0) := by
    apply NNReal.eq
    change dist (t₁ : ℝ) (t₀ : ℝ) = (m : ℝ)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast ht₁))]
    simp [t₁]
  have hXlaw : HasLaw X (gaussianReal 0 (m : ℝ≥0)) P := by
    rw [← hvar]
    exact hB.hasLaw_sub t₁ t₀
  let A : Set (Fin (r + 1) → ℝ) := {u | ∀ j, -barrier ≤ u j}
  let C : Set (Fin (r + 1) → ℝ) := {v | ∀ j, v j ≤ y + 1}
  have hA : MeasurableSet A := by
    rw [show A = ⋂ j : Fin (r + 1), {u : Fin (r + 1) → ℝ | -barrier ≤ u j} by ext u; simp [A]]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply j)
  have hC : MeasurableSet C := by
    rw [show C = ⋂ j : Fin (r + 1), {v : Fin (r + 1) → ℝ | v j ≤ y + 1} by ext v; simp [C]]
    exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const
  let f (u : Fin (r + 1) → ℝ) := u (Fin.last r)
  let g (v : Fin (r + 1) → ℝ) := v (Fin.last r)
  have hf : Measurable f := measurable_pi_apply _
  have hg : Measurable g := measurable_pi_apply _
  have hApre : U ⁻¹' A = survives B r barrier := by rfl
  have hCpre : V ⁻¹' C = survives (-Vproc) r (y + 1) := by ext ω; simp [V, C, survives]
  have hCprob : (P.map V) C = P (survives B r (y + 1)) := by
    rw [Measure.map_apply_of_aemeasurable hV hC, hCpre, survives_prob_eq hVproc.neg hB]
  have hAprob : (P.map U) A = P (survives B r barrier) := by
    rw [Measure.map_apply_of_aemeasurable hU hA, hApre]
  have hJoin : P.map (fun ω => (V ω, (U ω, X ω))) = (P.map V).prod ((P.map U).prod (gaussianReal 0 (m : ℝ≥0))) := by
    rw [hVUX.map_prod_eq_prod_map_map hV (hU.prodMk hX),
      hUX.map_prod_eq_prod_map_map hU hX, hXlaw.map_eq]
  have hEndpoint (ω : Ω) : f (U ω) + X ω + g (V ω) = B t₂ ω := by
    simp [f, U, X, g, V, Vproc, reversePrefix, Cstep, shiftAfter, t₂, t₀]
  have hSubset : centeredEndpoint B (r + m + r) barrier y ⊆
      (fun ω => (V ω, (U ω, X ω))) ⁻¹' tripleWindow A C f g (y - barrier) := by
    intro ω hω
    have hS := hω.1
    have hI : B t₂ ω ∈ Icc (y - barrier) (y - barrier + 1) := by rw [← ht₂]; exact hω.2
    change (∀ j : Fin (r + 1), V ω j ≤ y + 1) ∧
      (∀ j : Fin (r + 1), -barrier ≤ U ω j) ∧
      X ω ∈ Icc (y - barrier - f (U ω) - g (V ω)) (y - barrier - f (U ω) - g (V ω) + 1)
    refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
    · intro j
      have hj : (j.val : ℝ≥0) ≤ t₀ := by
        change (j.val : ℝ≥0) ≤ (r : ℝ≥0)
        exact_mod_cast (show j.val ≤ r by omega)
      let k : Fin (r + m + r + 1) := ⟨r + m + r - j.val, by omega⟩
      have hk : (k.val : ℝ≥0) = t₁ + (t₀ - (j.val : ℝ≥0)) := by
        change ((r + m + r - j.val : ℕ) : ℝ≥0) = _
        rw [natCast_sub_nnreal (by omega), ht₂]
        dsimp [t₂]
        rw [add_tsub_assoc_of_le hj]
      have hv : V ω j = B t₂ ω - B (k.val : ℝ≥0) ω := by
        unfold V Vproc reversePrefix Cstep shiftAfter
        rw [max_eq_left hj, ← hk]
        dsimp [t₂]
        ring
      have hpos : -barrier ≤ B (k.val : ℝ≥0) ω := hS k
      rw [hv]
      linarith [hI.2]
    · intro j
      exact hS ⟨j.val, by omega⟩
    · have h := hEndpoint ω
      change y - barrier - f (U ω) - g (V ω) ≤ X ω
      linarith [hI.1]
    · have h := hEndpoint ω
      change X ω ≤ y - barrier - f (U ω) - g (V ω) + 1
      linarith [hI.2]
  have hBound : P (centeredEndpoint B (r + m + r) barrier y) ≤
      ENNReal.ofReal (Real.sqrt (m : ℝ))⁻¹ * P (survives B r barrier) * P (survives B r (y + 1)) := by
    have hMeas := tripleWindow_meas hA hC hf hg (y - barrier)
    letI : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU
    calc
      _ ≤ P ((fun ω => (V ω, (U ω, X ω))) ⁻¹' tripleWindow A C f g (y - barrier)) := measure_mono hSubset
      _ = ((P.map V).prod ((P.map U).prod (gaussianReal 0 (m : ℝ≥0)))) (tripleWindow A C f g (y - barrier)) := by
        rw [← Measure.map_apply_of_aemeasurable (hV.prodMk (hU.prodMk hX)) hMeas, hJoin]
      _ ≤ _ := by
        have h := tripleWindow_le (P.map U) (P.map V) (m : ℝ≥0) (by exact_mod_cast hm.ne')
          hA hC hf hg (y - barrier)
        simpa only [hAprob, hCprob, NNReal.coe_natCast] using h
  have htop : ENNReal.ofReal (Real.sqrt (m : ℝ))⁻¹ *
      P (survives B r barrier) * P (survives B r (y + 1)) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _))
      (measure_ne_top P _)
  simpa only [measureReal_def, survivalProbability, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Real.sqrt (m : ℝ))⁻¹)] using
      ENNReal.toReal_mono htop hBound

private lemma inverse_le_two_div {v u : ℝ} (hv : 0 < v) (hu : 0 < u) (h : u ≤ 2 * v) :
    v⁻¹ ≤ 2 / u := by
  rw [← one_div, div_le_div_iff₀ hv hu, one_mul]
  exact h

theorem centeredEndpoint_polynomial_bound (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 1 ≤ n)
    {barrier y : ℝ} (hb : 0 ≤ barrier) (hy : 0 ≤ y) :
    P.real (centeredEndpoint B n barrier y) ≤
      (5184 / gaussianSeedProbability ^ 2) * (1 + barrier) * (1 + y) /
      (Real.sqrt ((n : ℝ) + 1)) ^ 3 := by
  let r := n / 3
  let m := n - r - r
  have hm : 0 < m := by unfold m r; omega
  have hdecomp : r + m + r = n := by unfold m r; omega
  have hrr : n + 1 ≤ 4 * (r + 1) := by unfold r; omega
  have hmm : n + 1 ≤ 4 * m := by unfold m r; omega
  let u := Real.sqrt ((n : ℝ) + 1)
  let v := Real.sqrt ((r : ℝ) + 1)
  let w := Real.sqrt (m : ℝ)
  let c := gaussianSeedProbability
  have hc : 0 < c := gaussianSeedProbability_pos
  have hu : 0 < u := by unfold u; positivity
  have hv : 0 < v := by unfold v; positivity
  have hw : 0 < w := by unfold w; exact Real.sqrt_pos.2 (by exact_mod_cast hm)
  have huv : u ≤ 2 * v := by
    dsimp [u, v]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity), show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact_mod_cast hrr
  have huw : u ≤ 2 * w := by
    dsimp [u, w]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity), show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact_mod_cast hmm
  have hinvV := inverse_le_two_div hv hu huv
  have hinvW := inverse_le_two_div hw hu huw
  have hA : survivalProbability B P r barrier ≤ (18 / c) * (1 + barrier) * (2 / u) := by
    calc
      _ ≤ (18 / c) * (1 + barrier) / v := survivalProbability_barrier_upper hB r hb
      _ ≤ _ := by
        rw [div_eq_mul_inv ((18 / c) * (1 + barrier)) v]
        exact mul_le_mul_of_nonneg_left hinvV (by positivity)
  have hB' : survivalProbability B P r (y + 1) ≤ (36 / c) * (1 + y) * (2 / u) := by
    have h := survivalProbability_barrier_upper hB r (show 0 ≤ y + 1 by linarith)
    change survivalProbability B P r (y + 1) ≤ _ at h
    calc
      _ ≤ (18 / c) * (1 + (y + 1)) / v := h
      _ ≤ (36 / c) * (1 + y) * (2 / u) := by
        rw [div_eq_mul_inv ((18 / c) * (1 + (y + 1))) v]
        have hy' : (18 / c) * (1 + (y + 1)) ≤ (36 / c) * (1 + y) := by
          apply (mul_le_mul_iff_left₀ hc).1
          have e₁ : 18 / c * (1 + (y + 1)) * c = 18 * (1 + (y + 1)) := by field_simp
          have e₂ : 36 / c * (1 + y) * c = 36 * (1 + y) := by field_simp
          rw [e₁, e₂]
          linarith
        exact mul_le_mul hy' hinvV (by positivity) (by positivity)
  have hAA : 0 ≤ survivalProbability B P r barrier := survivalProbability_nonneg r barrier
  have hBB : 0 ≤ survivalProbability B P r (y + 1) := survivalProbability_nonneg r (y + 1)
  calc
    P.real (centeredEndpoint B n barrier y) ≤ w⁻¹ * survivalProbability B P r barrier *
        survivalProbability B P r (y + 1) := by
      rw [← hdecomp]
      exact centeredEndpoint_three_blocks hB r m hm barrier y
    _ ≤ (2 / u) * ((18 / c) * (1 + barrier) * (2 / u)) * ((36 / c) * (1 + y) * (2 / u)) :=
      mul_le_mul (mul_le_mul hinvW hA hAA (by positivity)) hB' hBB (by positivity)
    _ = _ := by
      change (2 / u) * ((18 / c) * (1 + barrier) * (2 / u)) *
        ((36 / c) * (1 + y) * (2 / u)) = (5184 / c ^ 2) * (1 + barrier) * (1 + y) / u ^ 3
      field_simp
      <;> ring

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

noncomputable def driftWeight (δ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (δ * x - δ ^ 2 * (v : ℝ) / 2))

private lemma driftWeight_meas (δ : ℝ) (v : ℝ≥0) : Measurable (driftWeight δ v) := by
  unfold driftWeight
  fun_prop

private lemma gaussian_pdf_drift (δ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDF (δ * (v : ℝ)) v x = gaussianPDF 0 v x * driftWeight δ v x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  simp only [gaussianPDF, driftWeight]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
  congr 1
  unfold gaussianPDFReal
  have h : -(x - δ * (v : ℝ)) ^ 2 / (2 * (v : ℝ)) =
      -(x - 0) ^ 2 / (2 * (v : ℝ)) + (δ * x - δ ^ 2 * (v : ℝ) / 2) := by
    field_simp
    <;> ring
  rw [h, Real.exp_add]
  ring

/-- Shifting a Gaussian of variance v by δv multiplies its likelihood by exp(δx−δ²v/2). -/
theorem gaussianReal_drift_withDensity (δ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal (δ * (v : ℝ)) v = (gaussianReal 0 v).withDensity (driftWeight δ v) := by
  ext s hs
  rw [gaussianReal_apply _ hv s, withDensity_apply _ hs, gaussianReal_of_var_ne_zero 0 hv,
    setLIntegral_withDensity_eq_setLIntegral_mul volume (measurable_gaussianPDF _ _)
      (driftWeight_meas δ v) hs]
  exact lintegral_congr (gaussian_pdf_drift δ hv)

theorem gaussianReal_negative_drift_interval_upper {d a : ℝ} (hd : 0 ≤ d)
    {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) (ha : s ⊆ Ici a) :
    gaussianReal (-d * (v : ℝ)) v s ≤ driftWeight (-d) v a * gaussianReal 0 v s := by
  rw [gaussianReal_drift_withDensity (-d) hv, withDensity_apply _ hs,
    ← Measure.restrict_apply_univ (s := s), ← lintegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  have hax : a ≤ x := ha hx
  unfold driftWeight
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith [mul_le_mul_of_nonneg_left hax hd]

theorem gaussianReal_negative_drift_interval_lower {d b : ℝ} (hd : 0 ≤ d)
    {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) (hb : s ⊆ Iic b) :
    driftWeight (-d) v b * gaussianReal 0 v s ≤ gaussianReal (-d * (v : ℝ)) v s := by
  rw [gaussianReal_drift_withDensity (-d) hv, withDensity_apply _ hs,
    ← Measure.restrict_apply_univ (s := s), ← lintegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  have hxb : x ≤ b := hb hx
  unfold driftWeight
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith [mul_le_mul_of_nonneg_left hxb hd]

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

private lemma negGaussian_product_window {U : Type*} [MeasurableSpace U]
    (μ : Measure U) {A : Set (U × ℝ)} (hA : MeasurableSet A)
    {d a b : ℝ} (hd : 0 ≤ d) (hab : ∀ z ∈ A, z.2 ∈ Icc a b)
    {v : ℝ≥0} (hv : v ≠ 0) :
    driftWeight (-d) v b * (μ.prod (gaussianReal 0 v)) A ≤ (μ.prod (gaussianReal (-d * (v : ℝ)) v)) A ∧
    (μ.prod (gaussianReal (-d * (v : ℝ)) v)) A ≤ driftWeight (-d) v a * (μ.prod (gaussianReal 0 v)) A := by
  have hfiber (u : U) : MeasurableSet (Prod.mk u ⁻¹' A) := (measurable_const.prodMk measurable_id) hA
  have hfiberA (u : U) : Prod.mk u ⁻¹' A ⊆ Ici a := fun x hx => (hab (u, x) hx).1
  have hfiberB (u : U) : Prod.mk u ⁻¹' A ⊆ Iic b := fun x hx => (hab (u, x) hx).2
  rw [Measure.prod_apply hA, Measure.prod_apply hA, ← lintegral_const_mul' _ _ (by simp [driftWeight]),
    ← lintegral_const_mul' _ _ (by simp [driftWeight])]
  exact ⟨lintegral_mono fun u => gaussianReal_negative_drift_interval_lower hd hv (hfiber u) (hfiberB u),
    lintegral_mono fun u => gaussianReal_negative_drift_interval_upper hd hv (hfiber u) (hfiberA u)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

def driftedPath (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω - d * (t : ℝ)

theorem negative_driftEndpoint_bounds (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    {d : ℝ} (hd : 0 ≤ d) (barrier y : ℝ) :
    driftWeight (-d) n (y - barrier + 1) * P (centeredEndpoint B n barrier y) ≤
      P (centeredEndpoint (driftedPath B d) n barrier y) ∧
    P (centeredEndpoint (driftedPath B d) n barrier y) ≤
      driftWeight (-d) n (y - barrier) * P (centeredEndpoint B n barrier y) := by
  let V (ω : Ω) (j : Fin (n + 1)) := walkBridge B j ω
  let X := B (n : ℝ≥0)
  let Xd (ω : Ω) := X ω - d * (n : ℝ)
  let A : Set ((Fin (n + 1) → ℝ) × ℝ) :=
    {z | (∀ j : Fin (n + 1), -barrier ≤ z.1 j + gridFraction j * z.2) ∧
      z.2 ∈ Icc (y - barrier) (y - barrier + 1)}
  have hV : AEMeasurable V P := aemeasurable_pi_lambda _ (aemeasurable_walkBridge hB)
  have hX : AEMeasurable X P := hB.aemeasurable _
  have hXd : AEMeasurable Xd P := hX.sub aemeasurable_const
  have hMeas : MeasurableSet A := by
    rw [show A = (⋂ j : Fin (n + 1), {z : (Fin (n + 1) → ℝ) × ℝ |
        -barrier ≤ z.1 j + gridFraction j * z.2}) ∩
        {z : (Fin (n + 1) → ℝ) × ℝ | z.2 ∈ Icc (y - barrier) (y - barrier + 1)} by ext z; simp [A]]
    refine (MeasurableSet.iInter fun j => measurableSet_le measurable_const
      (((measurable_pi_apply j).comp measurable_fst).add (measurable_const.mul measurable_snd))).inter ?_
    exact measurable_snd measurableSet_Icc
  have hIndep := indepFun_walkBridge_endpoint hB hn
  change IndepFun V X P at hIndep
  have hIndepD : IndepFun V Xd P :=
    hIndep.comp measurable_id (measurable_id.sub_const (d * (n : ℝ)))
  have hXlaw : HasLaw X (gaussianReal 0 n) P := hB.hasLaw_eval _
  have hXdlaw : HasLaw Xd (gaussianReal (-d * (n : ℝ)) n) P := by
    convert gaussianReal_add_const hXlaw (-(d * (n : ℝ))) using 1 <;> simp [Xd, sub_eq_add_neg]
  have hMap : (P.map (fun ω => (V ω, X ω))) = (P.map V).prod (gaussianReal 0 n) := by
    rw [hIndep.map_prod_eq_prod_map_map hV hX, hXlaw.map_eq]
  have hMapD : (P.map (fun ω => (V ω, Xd ω))) = (P.map V).prod (gaussianReal (-d * (n : ℝ)) n) := by
    rw [hIndepD.map_prod_eq_prod_map_map hV hXd, hXdlaw.map_eq]
  have hPre : (fun ω => (V ω, X ω)) ⁻¹' A = centeredEndpoint B n barrier y := by
    ext ω
    simp [A, V, X, walkBridge, centeredEndpoint, survives]
  have hCancel (j : Fin (n + 1)) (ω : Ω) :
      V ω j + gridFraction j * Xd ω = driftedPath B d (j.val : ℝ≥0) ω := by
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [V, walkBridge, gridFraction, Xd, X, driftedPath, NNReal.coe_natCast]
    field_simp
    <;> ring
  have hPreD : (fun ω => (V ω, Xd ω)) ⁻¹' A = centeredEndpoint (driftedPath B d) n barrier y := by
    ext ω
    change ((∀ j : Fin (n + 1), -barrier ≤ V ω j + gridFraction j * Xd ω) ∧
      Xd ω ∈ Icc (y - barrier) (y - barrier + 1)) ↔ _
    simp_rw [hCancel]
    rfl
  have hMain : (P.map V).prod (gaussianReal 0 n) A = P (centeredEndpoint B n barrier y) := by
    rw [← hMap, Measure.map_apply_of_aemeasurable (hV.prodMk hX) hMeas, hPre]
  have hDrift : (P.map V).prod (gaussianReal (-d * (n : ℝ)) n) A =
      P (centeredEndpoint (driftedPath B d) n barrier y) := by
    rw [← hMapD, Measure.map_apply_of_aemeasurable (hV.prodMk hXd) hMeas, hPreD]
  have hWindow (z : (Fin (n + 1) → ℝ) × ℝ) (hz : z ∈ A) :
      z.2 ∈ Icc (y - barrier) (y - barrier + 1) := hz.2
  have hcoe : ((n : ℝ≥0) : ℝ) = (n : ℝ) := NNReal.coe_natCast n
  have hb := negGaussian_product_window (P.map V) hMeas hd hWindow
    (v := (n : ℝ≥0)) (by exact_mod_cast hn.ne')
  simpa only [hcoe, hMain, hDrift] using hb

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

private noncomputable def tailSeriesTerm (d : ℝ) (k : ℕ) : ℝ :=
  (1 + (k : ℝ)) * Real.exp (-d * (k : ℝ))

private lemma tailSeriesTerm_nonneg (d : ℝ) (k : ℕ) : 0 ≤ tailSeriesTerm d k := by
  unfold tailSeriesTerm
  positivity

private lemma summable_tailSeriesTerm {d : ℝ} (hd : 0 < d) : Summable (tailSeriesTerm d) := by
  let r := Real.exp (-d)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have hs := (summable_geometric_of_norm_lt_one hr).add
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr)
  apply hs.congr
  intro k
  have h : Real.exp (-d * (k : ℝ)) = r ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
  simp only [tailSeriesTerm, h, pow_one, add_mul, one_mul]

noncomputable def driftSurvivalConstant (d : ℝ) : ℝ :=
  (5184 / gaussianSeedProbability ^ 2) * (∑' k, tailSeriesTerm d k)

lemma driftSurvivalConstant_pos {d : ℝ} (hd : 0 < d) : 0 < driftSurvivalConstant d := by
  have htsum : 0 < ∑' k, tailSeriesTerm d k := by
    have h := (summable_tailSeriesTerm hd).le_tsum 0 (fun k _ => tailSeriesTerm_nonneg d k)
    simpa [tailSeriesTerm] using (show 0 < tailSeriesTerm d 0 by simp [tailSeriesTerm]).trans_le h
  have hc := gaussianSeedProbability_pos
  unfold driftSurvivalConstant
  positivity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem drifted_survival_upper (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 1 ≤ n) {d : ℝ}
    (hd : 0 < d) {barrier : ℝ} (hb : 0 ≤ barrier) :
    survivalProbability (driftedPath B d) P n barrier ≤
      driftSurvivalConstant d * (1 + barrier) * Real.exp (d * barrier - d ^ 2 * (n : ℝ) / 2) /
        (Real.sqrt ((n : ℝ) + 1)) ^ 3 := by
  let U := (5184 / gaussianSeedProbability ^ 2) * (1 + barrier) *
    Real.exp (d * barrier - d ^ 2 * (n : ℝ) / 2) / (Real.sqrt ((n : ℝ) + 1)) ^ 3
  let E (k : ℕ) := centeredEndpoint (driftedPath B d) n barrier k
  have hU : 0 ≤ U := by unfold U; positivity
  have hCover : survives (driftedPath B d) n barrier ⊆ ⋃ k : ℕ, E k := by
    intro ω hω
    let z := driftedPath B d (n : ℝ≥0) ω + barrier
    have ha : -barrier ≤ driftedPath B d (n : ℝ≥0) ω := hω (Fin.last n)
    have hz : 0 ≤ z := by unfold z; linarith
    let k := ⌊z⌋₊
    refine mem_iUnion.mpr ⟨k, hω, ?_⟩
    have hlo : (k : ℝ) ≤ z := Nat.floor_le hz
    have hhi : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
    exact ⟨by dsimp [z] at hlo; linarith, by dsimp [z] at hhi; linarith⟩
  have hEach (k : ℕ) : P (E k) ≤ ENNReal.ofReal (U * tailSeriesTerm d k) := by
    have hcenter := centeredEndpoint_polynomial_bound hB hn hb (Nat.cast_nonneg (α := ℝ) k)
    let L := (5184 / gaussianSeedProbability ^ 2) * (1 + barrier) * (1 + (k : ℝ)) /
      (Real.sqrt ((n : ℝ) + 1)) ^ 3
    have hL : 0 ≤ L := by unfold L; positivity
    have hM : P (centeredEndpoint B n barrier k) ≤ ENNReal.ofReal L := by
      apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).1
      rw [ENNReal.toReal_ofReal hL]
      exact hcenter
    calc
      P (E k) ≤ driftWeight (-d) n ((k : ℝ) - barrier) * P (centeredEndpoint B n barrier k) :=
        (negative_driftEndpoint_bounds hB (by omega) hd.le barrier k).2
      _ ≤ driftWeight (-d) n ((k : ℝ) - barrier) * ENNReal.ofReal L := by gcongr
      _ = ENNReal.ofReal (U * tailSeriesTerm d k) := by
        unfold driftWeight U L tailSeriesTerm
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        rw [show -d * ((k : ℝ) - barrier) - (-d) ^ 2 * ((n : ℝ≥0) : ℝ) / 2 =
          (d * barrier - d ^ 2 * (n : ℝ) / 2) + -d * (k : ℝ) by
            simp only [NNReal.coe_natCast]; ring,
          Real.exp_add]
        ring
  have hs : Summable (fun k => U * tailSeriesTerm d k) := (summable_tailSeriesTerm hd).mul_left U
  have hSum :
      P (survives (driftedPath B d) n barrier) ≤ ENNReal.ofReal (U * (∑' k, tailSeriesTerm d k)) := by
    calc
      _ ≤ P (⋃ k : ℕ, E k) := measure_mono hCover
      _ ≤ ∑' k, P (E k) := measure_iUnion_le _
      _ ≤ ∑' k, ENNReal.ofReal (U * tailSeriesTerm d k) := ENNReal.tsum_le_tsum hEach
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hU (tailSeriesTerm_nonneg d k)) hs,
          (summable_tailSeriesTerm hd).tsum_mul_left]
  have hf : 0 ≤ U * (∑' k, tailSeriesTerm d k) :=
    mul_nonneg hU (tsum_nonneg (tailSeriesTerm_nonneg d))
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSum
  rw [ENNReal.toReal_ofReal hf] at hReal
  refine hReal.trans_eq ?_
  unfold U driftSurvivalConstant
  ring

def latticeRecord (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j : Fin (n + 1),
    driftedPath B d (j.val : ℝ≥0) ω ≤ driftedPath B d (n : ℝ≥0) ω}

private lemma drifted_reversePrefix_eq_sub (B : ℝ≥0 → Ω → ℝ) (d : ℝ)
    {t n : ℝ≥0} (ht : t ≤ n) (ω : Ω) :
    driftedPath (reversePrefix B n) d t ω =
      driftedPath B d n ω - driftedPath B d (n - t) ω := by
  simp only [driftedPath, reversePrefix, max_eq_left ht, NNReal.coe_sub ht]
  ring

lemma latticeRecord_eq_survives_reverse (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (n : ℕ) :
    latticeRecord B d n = survives (driftedPath (reversePrefix B (n : ℝ≥0)) d) n 0 := by
  ext ω
  change (∀ j : Fin (n + 1),
    driftedPath B d (j.val : ℝ≥0) ω ≤ driftedPath B d (n : ℝ≥0) ω) ↔
    (∀ j : Fin (n + 1), -(0 : ℝ) ≤ driftedPath (reversePrefix B (n : ℝ≥0)) d (j.val : ℝ≥0) ω)
  rw [neg_zero]
  constructor
  · intro h j
    have hj : j.val ≤ n := by omega
    have hj' : (j.val : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hj
    rw [drifted_reversePrefix_eq_sub B d hj' ω, sub_nonneg, ← natCast_sub_nnreal hj]
    exact h ⟨n - j.val, by omega⟩
  · intro h j
    have hj : j.val ≤ n := by omega
    let i : Fin (n + 1) := ⟨n - j.val, by omega⟩
    have hi' : (i.val : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast (show i.val ≤ n by omega)
    have hle := h i
    rw [drifted_reversePrefix_eq_sub B d hi' ω, sub_nonneg] at hle
    simpa only [i, cast_sub_index hj] using hle

theorem latticeRecord_upper (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 1 ≤ n)
    {d : ℝ} (hd : 0 < d) :
    P.real (latticeRecord B d n) ≤ driftSurvivalConstant d * Real.exp (-(d ^ 2 * (n : ℝ) / 2)) /
      (Real.sqrt ((n : ℝ) + 1)) ^ 3 := by
  have h := drifted_survival_upper (preBrownian_reversePrefix hB (n : ℝ≥0)) hn hd (barrier := 0) le_rfl
  rw [latticeRecord_eq_survives_reverse]
  simpa [survivalProbability] using h

end GaussianWalkSurvival
namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

private lemma lintegral_driftWeight_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (δ : ℝ) :
    (∫⁻ ω, driftWeight δ v (X ω) ∂P) = 1 := by
  rw [hX.lintegral_comp (driftWeight_meas δ v).aemeasurable]
  by_cases hv : v = 0
  · subst v
    rw [gaussianReal_zero_var, lintegral_dirac' _ (driftWeight_meas δ 0)]
    simp [driftWeight]
  · have h := congrArg (fun μ : Measure ℝ => μ univ) (gaussianReal_drift_withDensity δ hv)
    rwa [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, eq_comm] at h

private noncomputable def brownianWeight (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  driftWeight (2 * d) t (B t ω)

private lemma brownianWeight_eq (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (t : ℝ≥0) (ω : Ω) :
    brownianWeight B d t ω = ENNReal.ofReal (Real.exp (2 * d * driftedPath B d t ω)) := by
  unfold brownianWeight driftWeight driftedPath
  congr 2
  ring

private lemma brownianWeight_aemeasurable (hB : IsPreBrownianReal B P) (d : ℝ) (t : ℝ≥0) :
    AEMeasurable (brownianWeight B d t) P :=
  (driftWeight_meas (2 * d) t).comp_aemeasurable (hB.aemeasurable t)

private lemma brownianWeight_mul_shift (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (s r : ℝ≥0) (ω : Ω) :
    brownianWeight B d (s + r) ω =
      brownianWeight B d s ω * brownianWeight (shiftAfter B s) d r ω := by
  simp only [brownianWeight_eq]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  simp only [driftedPath, shiftAfter, NNReal.coe_add]
  ring

private lemma brownianWeight_setLIntegral_shift (hB : IsPreBrownianReal B P)
    (d : ℝ) (s r : ℝ≥0) {A : Set (Set.Iic s → ℝ)} (hA : MeasurableSet A)
    (hnull : NullMeasurableSet (pastProjection B s ⁻¹' A) P) :
    (∫⁻ ω in (pastProjection B s ⁻¹' A), brownianWeight B d (s + r) ω ∂P) =
      ∫⁻ ω in (pastProjection B s ⁻¹' A), brownianWeight B d s ω ∂P := by
  let E := pastProjection B s ⁻¹' A
  let f := E.indicator (brownianWeight B d s)
  let g := brownianWeight (shiftAfter B s) d r
  let indexS : Set.Iic s := ⟨s, mem_Iic.mpr le_rfl⟩
  let F (x : Set.Iic s → ℝ) := A.indicator (fun z => driftWeight (2 * d) s (z indexS)) x
  let G (x : ℝ≥0 → ℝ) := driftWeight (2 * d) r (x r)
  have hF : Measurable F := ((driftWeight_meas _ _).comp (measurable_pi_apply _)).indicator hA
  have hG : Measurable G := (driftWeight_meas _ _).comp (measurable_pi_apply _)
  have hf : f = F ∘ pastProjection B s := by
    funext ω
    change E.indicator (brownianWeight B d s) ω =
      A.indicator (fun z => driftWeight (2 * d) s (z indexS)) (pastProjection B s ω)
    by_cases h : ω ∈ E
    · have h' : pastProjection B s ω ∈ A := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      rfl
    · have h' : pastProjection B s ω ∉ A := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hIndep : IndepFun f g P := by
    rw [hf]
    exact (hB.indepFun_shift s).symm.comp hF hG
  have hfm : AEMeasurable f P := (brownianWeight_aemeasurable hB d s).indicator₀ hnull
  have hShift : IsPreBrownianReal (shiftAfter B s) P := hB.shift s
  have hgm : AEMeasurable g P := brownianWeight_aemeasurable hShift d r
  have hg : (∫⁻ ω, g ω ∂P) = 1 := lintegral_driftWeight_gaussian (hShift.hasLaw_eval r) (2 * d)
  calc
    _ = ∫⁻ ω, f ω * g ω ∂P := by
      rw [← lintegral_indicator₀ hnull]
      apply lintegral_congr
      intro ω
      change E.indicator (brownianWeight B d (s + r)) ω = f ω * g ω
      by_cases h : ω ∈ E
      · simp only [f, Set.indicator_of_mem h, g, brownianWeight_mul_shift]
      · simp only [f, Set.indicator_of_notMem h, zero_mul]
    _ = (∫⁻ ω, f ω ∂P) * ∫⁻ ω, g ω ∂P :=
      lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hfm hgm hIndep
    _ = _ := by rw [hg, mul_one, (lintegral_indicator₀ hnull (brownianWeight B d s))]

private def firstRiseCyl (I : Finset ℝ≥0) (d y : ℝ) (s : ℝ≥0) : Set (Set.Iic s → ℝ) :=
  {x | y < x ⟨s, mem_Iic.mpr le_rfl⟩ - d * (s : ℝ) ∧
    ∀ j : (I.filter (· < s)), x ⟨j.val, mem_Iic.mpr (Finset.mem_filter.mp j.property).2.le⟩ -
      d * (j.val : ℝ) ≤ y}

private def firstRise (B : ℝ≥0 → Ω → ℝ) (I : Finset ℝ≥0) (d y : ℝ) (s : ℝ≥0) : Set Ω :=
  pastProjection B s ⁻¹' firstRiseCyl I d y s

private lemma firstRise_mem {I : Finset ℝ≥0} {d y : ℝ} {s : ℝ≥0} {ω : Ω} :
    ω ∈ firstRise B I d y s ↔
      y < driftedPath B d s ω ∧ ∀ t ∈ I, t < s → driftedPath B d t ω ≤ y := by
  unfold firstRise firstRiseCyl pastProjection driftedPath
  change (_ ∧ (∀ j : (I.filter (· < s)), _)) ↔ _
  constructor
  · rintro ⟨h, hj⟩
    exact ⟨h, fun t ht hts => hj ⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩⟩⟩
  · rintro ⟨h, hj⟩
    exact ⟨h, fun t => hj t.val (Finset.mem_filter.mp t.property).1 (Finset.mem_filter.mp t.property).2⟩

private lemma firstRiseCyl_meas (I : Finset ℝ≥0) (d y : ℝ) (s : ℝ≥0) :
    MeasurableSet (firstRiseCyl I d y s) := by
  rw [show firstRiseCyl I d y s =
    {x : Set.Iic s → ℝ | y < x ⟨s, mem_Iic.mpr le_rfl⟩ - d * (s : ℝ)} ∩
      ⋂ j : (I.filter (· < s)), {x : Set.Iic s → ℝ |
        x ⟨j.val, mem_Iic.mpr (Finset.mem_filter.mp j.property).2.le⟩ - d * (j.val : ℝ) ≤ y} by
      ext x
      simp [firstRiseCyl]]
  exact (measurableSet_lt measurable_const ((measurable_pi_apply _).sub_const _)).inter
    (MeasurableSet.iInter fun _ => measurableSet_le ((measurable_pi_apply _).sub_const _) measurable_const)

private lemma firstRise_null (hB : IsPreBrownianReal B P) (I : Finset ℝ≥0) (d y : ℝ) (s : ℝ≥0) :
    NullMeasurableSet (firstRise B I d y s) P := by
  rw [show firstRise B I d y s = {ω | y < driftedPath B d s ω} ∩
      ⋂ j : (I.filter (· < s)), {ω | driftedPath B d j.val ω ≤ y} by
    ext ω
    simp [firstRise_mem, SetCoe.forall', Finset.mem_filter, and_imp]]
  exact (nullMeasurableSet_lt aemeasurable_const ((hB.aemeasurable s).sub aemeasurable_const)).inter
    (NullMeasurableSet.iInter fun j =>
      nullMeasurableSet_le ((hB.aemeasurable j.val).sub aemeasurable_const) aemeasurable_const)

private lemma firstRise_disjoint (I : Finset ℝ≥0) (d y : ℝ) :
    Pairwise (fun s t : I => Disjoint (firstRise B I d y s.val) (firstRise B I d y t.val)) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro ω hs ht
  obtain ⟨hs, hsp⟩ := firstRise_mem.mp hs
  obtain ⟨ht, htp⟩ := firstRise_mem.mp ht
  rcases lt_or_gt_of_ne (fun h : s.val = t.val => hst (Subtype.ext h)) with h | h
  · exact (not_lt_of_ge (htp s.val s.property h)) hs
  · exact (not_lt_of_ge (hsp t.val t.property h)) ht

private lemma iUnion_firstRise (I : Finset ℝ≥0) (d y : ℝ) :
    (⋃ s : I, firstRise B I d y s.val) = {ω | ∃ t ∈ I, y < driftedPath B d t ω} := by
  ext ω
  constructor
  · intro h
    obtain ⟨s, hs⟩ := mem_iUnion.mp h
    exact ⟨s.val, s.property, (firstRise_mem.mp hs).1⟩
  · intro h
    obtain ⟨t, ht, hty⟩ := h
    let J := I.filter (fun j => y < driftedPath B d j ω)
    have hJ : J.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨ht, hty⟩⟩
    let s := J.min' hJ
    have hmem : s ∈ J := Finset.min'_mem _ _
    obtain ⟨hs, hsy⟩ := Finset.mem_filter.mp hmem
    apply mem_iUnion.mpr
    refine ⟨⟨s, hs⟩, firstRise_mem.mpr ⟨hsy, ?_⟩⟩
    intro u hu hus
    by_contra! hn
    exact (not_lt_of_ge (J.min'_le u (Finset.mem_filter.mpr ⟨hu, hn⟩))) hus

theorem finite_rise_upper (hB : IsPreBrownianReal B P) {d : ℝ} (hd : 0 < d)
    (I : Finset ℝ≥0) (y : ℝ) :
    P {ω | ∃ t ∈ I, y < driftedPath B d t ω} ≤ ENNReal.ofReal (Real.exp (-(2 * d * y))) := by
  classical
  let c := ENNReal.ofReal (Real.exp (2 * d * y))
  have hc : c ≠ 0 := by unfold c; simp [Real.exp_pos]
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  let T := I.sup id
  let E (s : I) := firstRise B I d y s.val
  have hEs (s : I) : NullMeasurableSet (E s) P := firstRise_null hB I d y s.val
  have hEd : Pairwise (fun s t : I => AEDisjoint P (E s) (E t)) :=
    fun _ _ h => (firstRise_disjoint I d y h).aedisjoint
  have hL (s : I) : ∫⁻ _ in E s, c ∂P ≤ ∫⁻ ω in E s, brownianWeight B d s.val ω ∂P := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem₀ (hEs s)] with ω hω
    have hr := (firstRise_mem.mp hω).1
    rw [brownianWeight_eq]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hr.le (by positivity)))
  have hShift (s : I) : (∫⁻ ω in E s, brownianWeight B d s.val ω ∂P) =
      ∫⁻ ω in E s, brownianWeight B d T ω ∂P := by
    have hs : s.val ≤ T := Finset.le_sup (f := id) s.property
    have heq : s.val + (T - s.val) = T := by rw [add_comm, tsub_add_cancel_of_le hs]
    have h := brownianWeight_setLIntegral_shift hB d s.val (T - s.val)
      (firstRiseCyl_meas I d y s.val) (hEs s)
    rw [heq] at h
    exact h.symm
  have hSum : c * P (⋃ s : I, E s) ≤ 1 := calc
    _ = ∑' s : I, ∫⁻ _ in E s, c ∂P := by
      rw [← setLIntegral_const, lintegral_iUnion₀ hEs hEd]
    _ ≤ ∑' s : I, ∫⁻ ω in E s, brownianWeight B d s.val ω ∂P := ENNReal.tsum_le_tsum hL
    _ = ∫⁻ ω in (⋃ s : I, E s), brownianWeight B d T ω ∂P := by
      simp_rw [hShift, lintegral_iUnion₀ hEs hEd]
    _ ≤ ∫⁻ ω, brownianWeight B d T ω ∂P := by
      simpa only [Measure.restrict_univ] using lintegral_mono_set (μ := P)
        (f := brownianWeight B d T) (subset_univ (⋃ s : I, E s))
    _ = 1 := lintegral_driftWeight_gaussian (hB.hasLaw_eval T) (2 * d)
  rw [iUnion_firstRise I d y] at hSum
  apply (ENNReal.mul_le_mul_iff_right hc hctop).mp
  have hOne : c * ENNReal.ofReal (Real.exp (-(2 * d * y))) = 1 := by
    unfold c
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one]
  rwa [hOne]

def riseAbove (B : ℝ≥0 → Ω → ℝ) (d y : ℝ) : Set Ω :=
  {ω | ∃ t, y < driftedPath B d t ω}

def riseCyl (S : Set ℝ≥0) (d y : ℝ) : Set (ℝ≥0 → ℝ) :=
  {x | ∃ t ∈ S, y < x t - d * (t : ℝ)}

lemma riseCyl_meas {S : Set ℝ≥0} (hS : S.Countable) (d y : ℝ) :
    MeasurableSet (riseCyl S d y) := by
  letI := hS.to_subtype
  rw [show riseCyl S d y = ⋃ t : S, {x : ℝ≥0 → ℝ | y < x t.val - d * (t.val : ℝ)} by
    ext x
    simp [riseCyl]]
  exact MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const ((measurable_pi_apply _).sub_const _)

lemma riseAbove_ae_eq_dense (hB : IsBrownianReal B P) {S : Set ℝ≥0} (hS : Dense S) (d y : ℝ) :
    riseAbove B d y =ᵐ[P] (fun ω t => B t ω) ⁻¹' riseCyl S d y := by
  filter_upwards [hB.cont] with ω hω
  apply propext
  change (∃ t, y < driftedPath B d t ω) ↔ ∃ t ∈ S, y < driftedPath B d t ω
  constructor
  · rintro ⟨t, ht⟩
    let U := {s : ℝ≥0 | y < driftedPath B d s ω}
    have hU : IsOpen U :=
      isOpen_lt continuous_const (hω.sub (continuous_const.mul NNReal.continuous_coe))
    obtain ⟨r, hr, hrS⟩ := hS.inter_open_nonempty U hU ⟨t, ht⟩
    exact ⟨r, hrS, hr⟩
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩

/-- The drifted Brownian path exceeds a level with probability at most exp(-2 d y). -/
theorem continuous_rise_upper (hB : IsBrownianReal B P) {d : ℝ} (hd : 0 < d) (y : ℝ) :
    P (riseAbove B d y) ≤ ENNReal.ofReal (Real.exp (-(2 * d * y))) := by
  classical
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSd.nonempty
  let I (n : ℕ) := (Finset.range (n + 1)).image f
  let E (n : ℕ) : Set Ω := {ω | ∃ t ∈ I n, y < driftedPath B d t ω}
  have hmono : Monotone E := by
    intro m n hmn ω hω
    obtain ⟨t, ht, hy⟩ := hω
    obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ht
    exact ⟨t, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr
      ((Finset.mem_range.mp hk).trans_le (Nat.succ_le_succ hmn)), hkt⟩, hy⟩
  have heq : (fun ω t => B t ω) ⁻¹' riseCyl S d y = ⋃ n, E n := by
    ext ω
    change (∃ t ∈ S, y < driftedPath B d t ω) ↔ _
    rw [hf]
    constructor
    · rintro ⟨t, ⟨n, rfl⟩, ht⟩
      exact mem_iUnion.mpr ⟨n, f n, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩, ht⟩
    · intro h
      obtain ⟨n, t, ht, hy⟩ := mem_iUnion.mp h
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨f k, ⟨k, rfl⟩, hy⟩
  rw [measure_congr (riseAbove_ae_eq_dense hB hSd d y), heq, hmono.measure_iUnion]
  exact iSup_le fun n => finite_rise_upper hB.toIsPreBrownianReal hd (I n) y

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

private def shiftedValue (B : ℝ≥0 → Ω → ℝ) (h : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  h + B t ω

private lemma shiftedValue_aemeasurable (hB : IsPreBrownianReal B P) (h : ℝ) (t : ℝ≥0) :
    AEMeasurable (shiftedValue B h t) P :=
  aemeasurable_const.add (hB.aemeasurable t)

/-- At a deterministic time, the independent Gaussian increment can be reflected in every past event. -/
private lemma reflect_endpoint_on_past (hB : IsPreBrownianReal B P) {s T : ℝ≥0} (hs : s ≤ T)
    (h : ℝ) {A : Set (Set.Iic s → ℝ)} (hA : MeasurableSet A)
    (hnull : NullMeasurableSet (pastProjection B s ⁻¹' A) P) {W : Set ℝ} (hW : MeasurableSet W) :
    P ((pastProjection B s ⁻¹' A) ∩ {ω | shiftedValue B h T ω ∈ W}) =
      P ((pastProjection B s ⁻¹' A) ∩
        {ω | 2 * shiftedValue B h s ω - shiftedValue B h T ω ∈ W}) := by
  let E := pastProjection B s ⁻¹' A
  let J := fun ω => B T ω - B s ω
  let X (ω : Ω) := (shiftedValue B h s ω, E.indicator (fun _ => (1 : ℝ)) ω)
  let i : Set.Iic s := ⟨s, mem_Iic.mpr le_rfl⟩
  let F (v : Set.Iic s → ℝ) := (h + v i, A.indicator (fun _ => (1 : ℝ)) v)
  have hF : Measurable F := (measurable_const.add (measurable_pi_apply i)).prodMk
    (measurable_const.indicator hA)
  have hXF : X = F ∘ pastProjection B s := by
    funext ω
    change (h + B s ω, E.indicator (fun _ => (1 : ℝ)) ω) =
        (h + B s ω, A.indicator (fun _ => (1 : ℝ)) (pastProjection B s ω))
    congr 1
  have hmX : AEMeasurable X P := (shiftedValue_aemeasurable hB h s).prodMk
    (aemeasurable_const.indicator₀ hnull)
  have hmJ : AEMeasurable J P := (hB.aemeasurable T).sub (hB.aemeasurable s)
  have hAdd : s + (T - s) = T := by rw [add_comm, tsub_add_cancel_of_le hs]
  have hJ : HasLaw J (gaussianReal 0 (T - s)) P := by
    have hJ' := (hB.shift s).hasLaw_eval (T - s)
    rw [hAdd] at hJ'
    exact hJ'
  have hJN : HasLaw (-J) (gaussianReal 0 (T - s)) P := by
    simpa only [neg_zero] using gaussianReal_neg hJ
  have hI : IndepFun X J P := by
    rw [hXF]
    have h' := (hB.indepFun_shift s).symm.comp hF (measurable_pi_apply (T - s))
    change IndepFun (F ∘ pastProjection B s) (fun ω => B (s + (T - s)) ω - B s ω) P at h'
    rw [hAdd] at h'
    exact h'
  have hIN : IndepFun X (-J) P := hI.comp measurable_id measurable_neg
  have hMaps : P.map (fun ω => (X ω, J ω)) = P.map (fun ω => (X ω, (-J) ω)) := by
    rw [hI.map_prod_eq_prod_map_map hmX hmJ, hIN.map_prod_eq_prod_map_map hmX hmJ.neg,
      hJ.map_eq, hJN.map_eq]
  let L : Set ((ℝ × ℝ) × ℝ) := {p | p.1.2 = 1 ∧ p.1.1 + p.2 ∈ W}
  have hL : MeasurableSet L := by
    exact (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).inter
      (((measurable_fst.comp measurable_fst).add measurable_snd) hW)
  have hLpos : (fun ω => (X ω, J ω)) ⁻¹' L = E ∩ {ω | shiftedValue B h T ω ∈ W} := by
    ext ω
    change (E.indicator (fun _ => (1 : ℝ)) ω = 1 ∧ shiftedValue B h s ω + J ω ∈ W) ↔ _
    have hsum : shiftedValue B h s ω + J ω = shiftedValue B h T ω := by
      unfold shiftedValue J
      ring
    by_cases he : ω ∈ E <;> simp [he, hsum]
  have hLneg : (fun ω => (X ω, (-J) ω)) ⁻¹' L =
      E ∩ {ω | 2 * shiftedValue B h s ω - shiftedValue B h T ω ∈ W} := by
    ext ω
    change (E.indicator (fun _ => (1 : ℝ)) ω = 1 ∧ shiftedValue B h s ω + -J ω ∈ W) ↔ _
    have hsum : shiftedValue B h s ω + -J ω = 2 * shiftedValue B h s ω - shiftedValue B h T ω := by
      unfold shiftedValue J
      ring
    by_cases he : ω ∈ E <;> simp [he, hsum]
  calc
    _ = (P.map (fun ω => (X ω, J ω))) L := by
      rw [Measure.map_apply_of_aemeasurable (hmX.prodMk hmJ) hL, hLpos]
    _ = (P.map (fun ω => (X ω, (-J) ω))) L := by rw [hMaps]
    _ = _ := by rw [Measure.map_apply_of_aemeasurable (hmX.prodMk hmJ.neg) hL, hLneg]

private def goodCrossing (B : ℝ≥0 → Ω → ℝ) (I : Finset ℝ≥0) (h a ε : ℝ) (s : ℝ≥0) : Set Ω :=
  firstRise (-B) I 0 (h - a) s ∩ {ω | a - ε ≤ shiftedValue B h s ω}

private lemma goodCrossing_mem {I : Finset ℝ≥0} {h a ε : ℝ} {s : ℝ≥0} {ω : Ω} :
    ω ∈ goodCrossing B I h a ε s ↔
      shiftedValue B h s ω < a ∧ (∀ t ∈ I, t < s → a ≤ shiftedValue B h t ω) ∧
        a - ε ≤ shiftedValue B h s ω := by
  change (ω ∈ firstRise (-B) I 0 (h - a) s ∧ _) ↔ _
  rw [firstRise_mem]
  simp only [shiftedValue, driftedPath, Pi.neg_apply, zero_mul, sub_zero]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨by linarith, fun t ht hts => by linarith [h₂ t ht hts], h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨by linarith, fun t ht hts => by linarith [h₂ t ht hts]⟩, h₃⟩

private lemma goodCrossing_null (hB : IsPreBrownianReal B P) (I : Finset ℝ≥0)
    (h a ε : ℝ) (s : ℝ≥0) :
    NullMeasurableSet (goodCrossing B I h a ε s) P :=
  (firstRise_null hB.neg I 0 (h - a) s).inter
    (nullMeasurableSet_le aemeasurable_const (shiftedValue_aemeasurable hB h s))

private lemma goodCrossing_is_past (B : ℝ≥0 → Ω → ℝ) (I : Finset ℝ≥0) (h a ε : ℝ) (s : ℝ≥0) :
    ∃ A : Set (Set.Iic s → ℝ), MeasurableSet A ∧ goodCrossing B I h a ε s = pastProjection B s ⁻¹' A := by
  let i : Set.Iic s := ⟨s, mem_Iic.mpr le_rfl⟩
  let F := fun (v : Set.Iic s → ℝ) t => -v t
  let D : Set (Set.Iic s → ℝ) := {v | a - ε ≤ h + v i}
  have hF : Measurable F := measurable_pi_lambda _ (fun t => (measurable_pi_apply t).neg)
  have hD : MeasurableSet D := measurableSet_le measurable_const (measurable_const.add (measurable_pi_apply i))
  refine ⟨(F ⁻¹' firstRiseCyl I 0 (h - a) s) ∩ D,
    (hF (firstRiseCyl_meas I 0 (h - a) s)).inter hD, ?_⟩
  rfl

def finiteGoodCrossingTerminal (B : ℝ≥0 → Ω → ℝ) (I : Finset ℝ≥0)
    (h a ε l u : ℝ) (T : ℝ≥0) : Set Ω :=
  ⋃ s : I, goodCrossing B I h a ε s.val ∩ {ω | shiftedValue B h T ω ∈ Icc l u}

/-- Reflect the endpoint after the first sampled crossing whose overshoot is at most ε. -/
theorem finite_reflection_upper (hB : IsPreBrownianReal B P) (I : Finset ℝ≥0)
    (h a ε l u : ℝ) (T : ℝ≥0) (hI : ∀ s ∈ I, s ≤ T) :
    P (finiteGoodCrossingTerminal B I h a ε l u T) ≤
      P {ω | shiftedValue B h T ω ∈ Icc (2 * (a - ε) - u) (2 * a - l)} := by
  let L (s : I) := goodCrossing B I h a ε s.val ∩ {ω | shiftedValue B h T ω ∈ Icc l u}
  let R (s : I) := goodCrossing B I h a ε s.val ∩
    {ω | 2 * shiftedValue B h s.val ω - shiftedValue B h T ω ∈ Icc l u}
  have hLeft (s : I) : NullMeasurableSet (L s) P :=
    (goodCrossing_null hB I h a ε s.val).inter
      ((shiftedValue_aemeasurable hB h T).nullMeasurableSet_preimage measurableSet_Icc)
  have hRight (s : I) : NullMeasurableSet (R s) P :=
    (goodCrossing_null hB I h a ε s.val).inter
      (((aemeasurable_const.mul (shiftedValue_aemeasurable hB h s.val)).sub
        (shiftedValue_aemeasurable hB h T)).nullMeasurableSet_preimage measurableSet_Icc)
  have hdisj : Pairwise (fun s t : I => Disjoint
      (goodCrossing B I h a ε s.val) (goodCrossing B I h a ε t.val)) := by
    intro s t hst
    exact (firstRise_disjoint (B := -B) I 0 (h - a) hst).mono inter_subset_left inter_subset_left
  have hl : Pairwise (fun s t => AEDisjoint P (L s) (L t)) :=
    fun _ _ hst => ((hdisj hst).mono inter_subset_left inter_subset_left).aedisjoint
  have hr : Pairwise (fun s t => AEDisjoint P (R s) (R t)) :=
    fun _ _ hst => ((hdisj hst).mono inter_subset_left inter_subset_left).aedisjoint
  have hsame (s : I) : P (L s) = P (R s) := by
    obtain ⟨A, hA, hAe⟩ := goodCrossing_is_past B I h a ε s.val
    have hnull : NullMeasurableSet (pastProjection B s.val ⁻¹' A) P := by
      rw [← hAe]
      exact goodCrossing_null hB I h a ε s.val
    unfold L R
    rw [hAe]
    exact reflect_endpoint_on_past hB (hI s.val s.property) h hA hnull measurableSet_Icc
  calc
    _ = ∑' s : I, P (L s) := measure_iUnion₀ hl hLeft
    _ = ∑' s : I, P (R s) := tsum_congr hsame
    _ = P (⋃ s : I, R s) := (measure_iUnion₀ hr hRight).symm
    _ ≤ _ := by
      apply measure_mono
      intro ω hω
      obtain ⟨s, hb, hval⟩ := mem_iUnion.mp hω
      obtain ⟨hbelow, _, hover⟩ := goodCrossing_mem.mp hb
      change 2 * shiftedValue B h s.val ω - shiftedValue B h T ω ∈ Icc l u at hval
      exact ⟨by linarith [hval.2], by linarith [hval.1]⟩

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

private lemma dense_early_crossing {T : ℝ≥0} (times : ℕ → Set.Icc (0 : ℝ≥0) T)
    (hdense : DenseRange times) {f : ℝ≥0 → ℝ} (hf : Continuous f) {a ε : ℝ}
    (h0 : a ≤ f 0) (hε : 0 < ε) (hcross : ∃ t ≤ T, f t < a) :
    ∃ k, f (times k).val < a ∧ ∀ r ≤ (times k).val, a - ε ≤ f r := by
  let J : Set ℝ≥0 := Icc 0 T ∩ {s | f s ≤ a - ε}
  by_cases hJ : J.Nonempty
  · have hJc : IsCompact J := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
    obtain ⟨r, hr, hrmin⟩ := hJc.exists_isMinOn hJ continuous_id.continuousOn
    have hrt : r ≤ T := hr.1.2
    have hrf : f r ≤ a - ε := hr.2
    have hv : a - ε / 2 ∈ Icc (f r) (f 0) := ⟨by linarith, by linarith⟩
    obtain ⟨v, hvI, hfv⟩ := intermediate_value_Icc' (zero_le : 0 ≤ r) hf.continuousOn hv
    have hvr : v < r := by
      apply lt_of_le_of_ne hvI.2
      intro heq
      rw [heq] at hfv
      linarith
    let U : Set (Icc (0 : ℝ≥0) T) := {s | f s.val < a ∧ s.val < r}
    have hU : IsOpen U := by
      exact (isOpen_lt (hf.comp continuous_subtype_val) continuous_const).inter
        (isOpen_lt (f := fun s : Icc (0 : ℝ≥0) T => s.val) (g := fun _ => r)
          continuous_subtype_val continuous_const)
    have hUN : U.Nonempty := ⟨⟨v, hvI.1, hvr.le.trans hrt⟩, by
      change f v < a ∧ v < r
      exact ⟨by linarith, hvr⟩⟩
    obtain ⟨k, hk⟩ := hdense.exists_mem_open hU hUN
    refine ⟨k, hk.1, ?_⟩
    intro s hs
    have hsr : s < r := hs.trans_lt hk.2
    by_contra! hfs
    have hsJ : s ∈ J := ⟨⟨zero_le, hsr.le.trans hrt⟩, hfs.le⟩
    exact (not_lt_of_ge (hrmin hsJ)) hsr
  · let U : Set (Icc (0 : ℝ≥0) T) := {s | f s.val < a}
    have hU : IsOpen U := isOpen_lt (hf.comp continuous_subtype_val) continuous_const
    obtain ⟨t, ht, htf⟩ := hcross
    have hUN : U.Nonempty := ⟨⟨t, zero_le, ht⟩, htf⟩
    obtain ⟨k, hk⟩ := hdense.exists_mem_open hU hUN
    refine ⟨k, hk, ?_⟩
    intro r hr
    by_contra! hfr
    exact hJ ⟨r, ⟨⟨zero_le, hr.trans (times k).property.2⟩, hfr.le⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

def belowThenEndsIn (B : ℝ≥0 → Ω → ℝ) (h a l u : ℝ) (T : ℝ≥0) : Set Ω :=
  {ω | (∃ t ≤ T, shiftedValue B h t ω < a) ∧ shiftedValue B h T ω ∈ Icc l u}

private lemma finiteGoodCrossingTerminal_of_early (B : ℝ≥0 → Ω → ℝ) (I : Finset ℝ≥0)
    (h a ε l u : ℝ) (T : ℝ≥0) {ω : Ω} {t : ℝ≥0}
    (ht : t ∈ I) (hbelow : shiftedValue B h t ω < a)
    (hpre : ∀ r ≤ t, a - ε ≤ shiftedValue B h r ω)
    (hend : shiftedValue B h T ω ∈ Icc l u) :
    ω ∈ finiteGoodCrossingTerminal B I h a ε l u T := by
  classical
  let J := I.filter (fun s => shiftedValue B h s ω < a)
  have hJ : J.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨ht, hbelow⟩⟩
  let s := J.min' hJ
  have hsJ : s ∈ J := Finset.min'_mem _ _
  obtain ⟨hs, hsb⟩ := Finset.mem_filter.mp hsJ
  have hst : s ≤ t := J.min'_le _ (Finset.mem_filter.mpr ⟨ht, hbelow⟩)
  apply mem_iUnion.mpr
  refine ⟨⟨s, hs⟩, goodCrossing_mem.mpr ⟨hsb, ?_, hpre s hst⟩, hend⟩
  intro r hr hrs
  by_contra! h
  exact (not_lt_of_ge (J.min'_le _ (Finset.mem_filter.mpr ⟨hr, h⟩))) hrs

private lemma continuous_reflection_approx (hB : IsBrownianReal B P) {h a : ℝ} (hha : a ≤ h)
    {ε : ℝ} (hε : 0 < ε) (l u : ℝ) (T : ℝ≥0) :
    P (belowThenEndsIn B h a l u T) ≤
      P {ω | shiftedValue B h T ω ∈ Icc (2 * (a - ε) - u) (2 * a - l)} := by
  classical
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  let times := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ≥0) T)
  have hdense : DenseRange times := TopologicalSpace.denseRange_denseSeq _
  let I (n : ℕ) := (Finset.range (n + 1)).image (fun k => (times k).val)
  let E (n : ℕ) := finiteGoodCrossingTerminal B (I n) h a ε l u T
  let E' (n : ℕ) := ⋂ j ≥ n, E j
  have hE'm : Monotone E' := by
    intro m n hmn ω hω
    simp only [E', mem_iInter] at *
    intro j hj
    exact hω j (hmn.trans hj)
  have hAE : (belowThenEndsIn B h a l u T : Set Ω) ≤ᵐ[P] ((⋃ n, E' n) : Set Ω) := by
    filter_upwards [hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc hzero
    intro hω
    have hf : Continuous (fun t => shiftedValue B h t ω) := continuous_const.add hc
    have h0 : a ≤ shiftedValue B h 0 ω := by simpa only [shiftedValue, hzero, add_zero] using hha
    obtain ⟨k, hbelow, hpre⟩ := dense_early_crossing times hdense hf h0 hε hω.1
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    simp only [E', mem_iInter]
    intro j hj
    have ht : (times k).val ∈ I j :=
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
    exact finiteGoodCrossingTerminal_of_early B (I j) h a ε l u T ht hbelow hpre hω.2
  apply (measure_mono_ae hAE).trans
  rw [hE'm.measure_iUnion]
  apply iSup_le
  intro n
  refine (measure_mono (iInter₂_subset n le_rfl)).trans (finite_reflection_upper
    hB.toIsPreBrownianReal (I n) h a ε l u T ?_)
  intro s hs
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
  exact (times k).property.2

theorem continuous_reflection_upper (hB : IsBrownianReal B P) {h a : ℝ} (hha : a ≤ h)
    (l u : ℝ) (T : ℝ≥0) :
    P (belowThenEndsIn B h a l u T) ≤
      P {ω | shiftedValue B h T ω ∈ Icc (2 * a - u) (2 * a - l)} := by
  let ε (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  let E (n : ℕ) : Set Ω := {ω | shiftedValue B h T ω ∈ Icc (2 * (a - ε n) - u) (2 * a - l)}
  have hε (n : ℕ) : 0 < ε n := by unfold ε; positivity
  have hεm : Antitone ε := by
    intro j k hjk
    unfold ε
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hjk)
  have hEm : Antitone E := by
    intro j k hjk ω hω
    have h := hεm hjk
    exact ⟨by linarith [hω.1], hω.2⟩
  have hMeas (n : ℕ) : NullMeasurableSet (E n) P :=
    (shiftedValue_aemeasurable hB.toIsPreBrownianReal h T).nullMeasurableSet_preimage measurableSet_Icc
  have hs : (⋂ n, E n) = {ω | shiftedValue B h T ω ∈ Icc (2 * a - u) (2 * a - l)} := by
    ext ω
    simp only [mem_iInter, E, mem_ofPred_eq, mem_Icc]
    constructor
    · intro hω
      refine ⟨?_, (hω 0).2⟩
      by_contra! hh
      let g := 2 * a - u - shiftedValue B h T ω
      have hg : 0 < g := by unfold g; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (2 / g)
      have hc : (2 : ℝ) < ((n : ℝ) + 1) * g := by
        have hd := (div_lt_iff₀ hg).mp hn
        nlinarith
      have he : 2 * ε n < g := by
        unfold ε
        rw [← div_eq_mul_inv]
        exact (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr (by simpa [mul_comm] using hc)
      dsimp [g] at he
      linarith [(hω n).1]
    · intro hω n
      exact ⟨by linarith [hω.1, hε n], hω.2⟩
  rw [← hs, hEm.measure_iInter hMeas ⟨0, measure_ne_top P _⟩]
  exact le_iInf fun n => continuous_reflection_approx hB hha (hε n) l u T

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

private lemma gaussianReal_real_eq_integral {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    (gaussianReal 0 v).real s = ∫ x in s, gaussianPDFReal 0 v x := by
  unfold Measure.real
  rw [gaussianReal_apply_eq_integral _ hv s, ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x

private lemma centered_pdf_antitone {v : ℝ≥0} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 v y ≤ gaussianPDFReal 0 v x := by
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simp only [sub_zero]
  exact div_le_div_of_nonneg_right (neg_le_neg (pow_le_pow_left₀ hx hxy 2)) (by positivity)

private lemma gaussian_mass_lower {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ}
    (hs : MeasurableSet s) (hsf : volume s ≠ ∞) (c : ℝ)
    (hb : ∀ x ∈ s, c ≤ gaussianPDFReal 0 v x) :
    (volume s).toReal * c ≤ (gaussianReal 0 v).real s := by
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hsf⟩
  rw [gaussianReal_real_eq_integral hv]
  calc
    (volume s).toReal * c = ∫ _ in s, c := by simp [setIntegral_const, Measure.real]
    _ ≤ _ := integral_mono_ae (integrable_const _) (integrable_gaussianPDFReal _ _).restrict
      (by filter_upwards [ae_restrict_mem hs] with x hx using hb x hx)

private lemma gaussian_mass_upper {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ}
    (hs : MeasurableSet s) (hsf : volume s ≠ ∞) (c : ℝ)
    (hb : ∀ x ∈ s, gaussianPDFReal 0 v x ≤ c) :
    (gaussianReal 0 v).real s ≤ (volume s).toReal * c := by
  letI : IsFiniteMeasure (volume.restrict s) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hsf⟩
  rw [gaussianReal_real_eq_integral hv]
  calc
    _ ≤ ∫ _ in s, c := integral_mono_ae (integrable_gaussianPDFReal _ _).restrict (integrable_const _)
      (by filter_upwards [ae_restrict_mem hs] with x hx using hb x hx)
    _ = _ := by simp [setIntegral_const, Measure.real]

private lemma exp_gap_lower {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    z / 2 ≤ 1 - Real.exp (-z) := by
  have hexp : Real.exp (-z) ≤ (1 + z)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp z)
  calc
    _ ≤ z / (1 + z) := div_le_div_of_nonneg_left hz (by positivity) (by linarith)
    _ = 1 - (1 + z)⁻¹ := by
      have hz₀ : 1 + z ≠ 0 := by positivity
      field_simp
      <;> ring
    _ ≤ _ := by linarith

noncomputable def killedGaussianConstant : ℝ :=
  Real.exp (-(1 / 8)) * (3 / 32) / Real.sqrt (2 * Real.pi)

lemma killedGaussianConstant_pos : 0 < killedGaussianConstant := by unfold killedGaussianConstant; positivity

private lemma centered_pdf_gap_lower {v : ℝ≥0} (hv : 1 ≤ v) :
    killedGaussianConstant / (Real.sqrt (v : ℝ)) ^ 3 ≤
      (1 / 2) * (gaussianPDFReal 0 v (1 / 2) - gaussianPDFReal 0 v 1) := by
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hp : (0 : ℝ) < v := by linarith
  let z := 3 / (8 * (v : ℝ))
  have hz : 0 ≤ z := by unfold z; positivity
  have hz' : z ≤ 1 := by
    unfold z
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  let c := (Real.sqrt (2 * (Real.pi * (v : ℝ))))⁻¹
  have hc : 0 ≤ c := by unfold c; positivity
  have he : Real.exp (-(1 / 8)) ≤ Real.exp (-1 / (8 * (v : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 8) (by linarith : (8 : ℝ) ≤ 8 * (v : ℝ))
    simpa only [neg_div] using neg_le_neg h
  have hcalc : (1 / 2) * (gaussianPDFReal 0 v (1 / 2) - gaussianPDFReal 0 v 1) =
      (1 / 2) * c * Real.exp (-1 / (8 * (v : ℝ))) * (1 - Real.exp (-z)) := by
    unfold gaussianPDFReal c
    rw [show -((1 / 2 : ℝ) - 0) ^ 2 / (2 * (v : ℝ)) = -1 / (8 * (v : ℝ)) by ring,
      show -((1 : ℝ) - 0) ^ 2 / (2 * (v : ℝ)) = -1 / (8 * (v : ℝ)) + -z by
        unfold z
        field_simp
        <;> ring,
      Real.exp_add]
    ring
  rw [hcalc]
  calc
    _ = (1 / 2) * c * Real.exp (-(1 / 8)) * (z / 2) := by
      unfold killedGaussianConstant c z
      rw [show 2 * (Real.pi * (v : ℝ)) = (2 * Real.pi) * (v : ℝ) by ring,
        Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
      have hs : (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) := Real.sq_sqrt hp.le
      rw [← hs] at hp ⊢
      rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
      field_simp
      <;> ring
    _ ≤ _ := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) (exp_gap_lower hz hz')
        (by positivity) (by positivity)

theorem centered_gaussian_window_difference {v : ℝ≥0} (hv : 1 ≤ v) :
    killedGaussianConstant / (Real.sqrt (v : ℝ)) ^ 3 ≤
      (gaussianReal 0 v).real (Icc 0 1) - (gaussianReal 0 v).real (Icc 1 2) := by
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz] at hv
    norm_num at hv
  let μ := gaussianReal 0 v
  have h₁ := gaussian_mass_lower hv0 (s := Icc 0 (1 / 2 : ℝ)) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (gaussianPDFReal 0 v (1 / 2))
    (fun x hx => centered_pdf_antitone hx.1 hx.2)
  have h₂ := gaussian_mass_lower hv0 (s := Ioc (1 / 2 : ℝ) 1) measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (gaussianPDFReal 0 v 1)
    (fun x hx => centered_pdf_antitone (by linarith [hx.1]) hx.2)
  have h₃ := gaussian_mass_upper hv0 (s := Icc (1 : ℝ) 2) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (gaussianPDFReal 0 v 1)
    (fun x hx => centered_pdf_antitone (by norm_num) hx.1)
  rw [Real.volume_Icc, show (1 / 2 : ℝ) - 0 = 1 / 2 by ring,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h₁
  rw [Real.volume_Ioc, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h₂
  rw [Real.volume_Icc, show (2 : ℝ) - 1 = 1 by ring, ENNReal.ofReal_one, ENNReal.toReal_one, one_mul] at h₃
  have hsplit : μ.real (Icc 0 1) = μ.real (Icc 0 (1 / 2)) + μ.real (Ioc (1 / 2) 1) := by
    have hset : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Ioc (1 / 2) 1 := by
      ext x
      simp only [mem_Icc, mem_union, mem_Ioc]
      constructor
      · rintro ⟨hx, h1⟩
        rcases le_or_gt x (1 / 2) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨h, h1⟩
      · rintro (⟨hx, hh⟩ | ⟨hh, h1⟩) <;> constructor <;> linarith
    rw [hset, measureReal_union]
    · exact disjoint_left.mpr (fun x hx hx' => (not_lt_of_ge hx.2) hx'.1)
    · exact measurableSet_Ioc
  have hgap := centered_pdf_gap_lower hv
  change killedGaussianConstant / (Real.sqrt (v : ℝ)) ^ 3 ≤ μ.real (Icc 0 1) - μ.real (Icc 1 2)
  rw [hsplit]
  dsimp [μ] at *
  linarith

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

def closedWindow (B : ℝ≥0 → Ω → ℝ) (s T : ℝ≥0) (a l u : ℝ) : Set Ω :=
  {ω | (∀ t ∈ Icc s T, a ≤ B t ω) ∧ B T ω ∈ Icc l u}

private def closedWindowCyl (times : ℕ → ℝ≥0) (T : ℝ≥0) (a l u : ℝ) :
    Set (ℝ≥0 → ℝ) := {f | (∀ k, a ≤ f (times k)) ∧ f T ∈ Icc l u}

private lemma closedWindowCyl_meas (times : ℕ → ℝ≥0) (T : ℝ≥0) (a l u : ℝ) :
    MeasurableSet (closedWindowCyl times T a l u) := by
  rw [show closedWindowCyl times T a l u =
    (⋂ k, {f : ℝ≥0 → ℝ | a ≤ f (times k)}) ∩ {f | f T ∈ Icc l u} by
      ext f
      simp [closedWindowCyl]]
  exact (MeasurableSet.iInter fun k => measurableSet_le measurable_const
    (measurable_pi_apply (times k))).inter (measurable_pi_apply T measurableSet_Icc)

private lemma closedWindow_ae_eq_dense {s T : ℝ≥0}
    (times : ℕ → Icc s T) (htimes : DenseRange times)
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω)) (a l u : ℝ) :
    (closedWindow B s T a l u : Set Ω) =ᵐ[P]
      ((fun ω t => B t ω) ⁻¹' closedWindowCyl (fun k => (times k).val) T a l u : Set Ω) := by
  filter_upwards [hcont] with ω hc
  apply propext
  change ((∀ t ∈ Icc s T, a ≤ B t ω) ∧ B T ω ∈ Icc l u) ↔
    ((∀ k, a ≤ B (times k).val ω) ∧ B T ω ∈ Icc l u)
  constructor
  · intro h
    exact ⟨fun k => h.1 _ (times k).2, h.2⟩
  · intro h
    refine ⟨fun t ht => ?_, h.2⟩
    have hclosed : IsClosed {t : Icc s T | a ≤ B t.val ω} :=
      isClosed_le continuous_const (hc.comp continuous_subtype_val)
    exact htimes.induction_on (p := fun q : Icc s T => a ≤ B q.val ω) ⟨t, ht⟩ hclosed h.1

theorem centered_unit_window_lower (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 1 ≤ T) :
    killedGaussianConstant / (Real.sqrt (T : ℝ)) ^ 3 ≤
      P.real (closedWindow B 0 T (-1 / 2) 0 1) := by
  let G := closedWindow B 0 T (-1 / 2) 0 1
  let E := belowThenEndsIn B 1 (1 / 2) 1 2 T
  let A : Set Ω := {ω | B T ω ∈ Icc 0 1}
  let R : Set Ω := {ω | (-B T) ω ∈ Icc 1 2}
  have href : P E ≤ P R := by
    have h := continuous_reflection_upper hB (h := 1) (a := 1 / 2) (by norm_num) 1 2 T
    change P E ≤ _ at h
    convert h using 2
    ext ω
    simp only [R, Pi.neg_apply, mem_setOf_eq, mem_Icc, shiftedValue]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hG : A ⊆ E ∪ G := by
    intro ω hω
    by_cases h : ∀ t ∈ Icc (0 : ℝ≥0) T, -1 / 2 ≤ B t ω
    · exact Or.inr ⟨h, hω⟩
    · push Not at h
      obtain ⟨t, ht, hbelow⟩ := h
      change B T ω ∈ Icc (0 : ℝ) 1 at hω
      exact Or.inl ⟨⟨t, ht.2, by unfold shiftedValue; linarith⟩,
        ⟨by unfold shiftedValue; linarith [hω.1],
          by unfold shiftedValue; linarith [hω.2]⟩⟩
  have hA : P.real A = (gaussianReal 0 T).real (Icc 0 1) :=
    (hB.toIsPreBrownianReal.hasLaw_eval T).measureReal_eq measurableSet_Icc
  have hNeg : HasLaw (-B T) (gaussianReal 0 T) P := by
    simpa only [neg_zero] using gaussianReal_neg (hB.toIsPreBrownianReal.hasLaw_eval T)
  have hR : P.real R = (gaussianReal 0 T).real (Icc 1 2) :=
    hNeg.measureReal_eq measurableSet_Icc
  have hsum := (measureReal_mono (μ := P) hG).trans (measureReal_union_le E G)
  have hcross : P.real E ≤ P.real R :=
    (ENNReal.toReal_le_toReal (measure_ne_top P E) (measure_ne_top P R)).2 href
  have hdiff := centered_gaussian_window_difference hT
  rw [← hA, ← hR] at hdiff
  change _ ≤ P.real G
  linarith

private noncomputable def unitWindowSeed : ℝ := (gaussianReal 0 1).real (Icc 1 2)

private lemma unitWindowSeed_pos : 0 < unitWindowSeed := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  intro h
  have hv := (gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)) h
  rw [Real.volume_Icc, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_one] at hv
  exact one_ne_zero hv

noncomputable def centeredWindowConstant : ℝ := unitWindowSeed * killedGaussianConstant

lemma centeredWindowConstant_pos : 0 < centeredWindowConstant :=
  mul_pos unitWindowSeed_pos killedGaussianConstant_pos

theorem centered_window_lower (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 2 ≤ T) :
    centeredWindowConstant / (Real.sqrt (T : ℝ)) ^ 3 ≤
      P.real (closedWindow B 1 T (1 / 2) 1 3) := by
  let A : Set Ω := {ω | B 1 ω ∈ Icc 1 2}
  let R := T - 1
  let C := shiftAfter B 1
  let G := closedWindow C 0 R (-1 / 2) 0 1
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_tsub_of_add_le_right (by rwa [show (1 : ℝ≥0) + 1 = 2 by norm_num])
  have hC : IsBrownianReal C P := hB.shift 1
  have hA : P.real A = unitWindowSeed :=
    (hB.toIsPreBrownianReal.hasLaw_eval 1).measureReal_eq measurableSet_Icc
  letI : Nonempty (Icc (0 : ℝ≥0) R) := ⟨⟨0, by simp⟩⟩
  let times := TopologicalSpace.denseSeq (Icc (0 : ℝ≥0) R)
  let CY := closedWindowCyl (fun k => (times k).val) R (-1 / 2) 0 1
  have hCY : MeasurableSet CY := closedWindowCyl_meas _ _ _ _ _
  have hGae := closedWindow_ae_eq_dense times (TopologicalSpace.denseRange_denseSeq _) hC.cont
    (-1 / 2) 0 1
  have hAG : P.real (A ∩ G) = P.real A * P.real G := by
    let i : Iic (1 : ℝ≥0) := ⟨1, mem_Iic.mpr le_rfl⟩
    have hI : IndepFun (B 1) (fun ω t => C t ω) P :=
      (hB.toIsPreBrownianReal.indepFun_shift 1).symm.comp (measurable_pi_apply i) measurable_id
    have hmul := hI.measure_inter_preimage_eq_mul _ _ (measurableSet_Icc (a := (1 : ℝ)) (b := 2)) hCY
    change P (A ∩ ((fun ω t => C t ω) ⁻¹' CY)) = P A * P ((fun ω t => C t ω) ⁻¹' CY) at hmul
    have hae : ((A ∩ G) : Set Ω) =ᵐ[P] ((A ∩ ((fun ω t => C t ω) ⁻¹' CY)) : Set Ω) := by
      filter_upwards [hGae] with ω hω
      exact congrArg (fun p : Prop => (ω ∈ A) ∧ p) hω
    unfold Measure.real
    rw [measure_congr hae, hmul, ENNReal.toReal_mul, measure_congr hGae]
  have hSub : A ∩ G ⊆ closedWindow B 1 T (1 / 2) 1 3 := by
    rintro ω ⟨hωA, hωG⟩
    change B 1 ω ∈ Icc (1 : ℝ) 2 at hωA
    change ((∀ t ∈ Icc (0 : ℝ≥0) R, -1 / 2 ≤ C t ω) ∧ C R ω ∈ Icc 0 1) at hωG
    constructor
    · intro t ht
      have hts : 1 + (t - 1) = t := add_tsub_cancel_of_le ht.1
      have h := hωG.1 (t - 1) ⟨zero_le, tsub_le_tsub_right ht.2 _⟩
      change -1 / 2 ≤ B (1 + (t - 1)) ω - B 1 ω at h
      rw [hts] at h
      linarith [hωA.1]
    · have hts : 1 + R = T := add_tsub_cancel_of_le ((by norm_num : (1 : ℝ≥0) ≤ 2).trans hT)
      have h := hωG.2
      change B (1 + R) ω - B 1 ω ∈ Icc (0 : ℝ) 1 at h
      rw [hts] at h
      exact ⟨by linarith [hωA.1, h.1], by linarith [hωA.2, h.2]⟩
  have hbound := centered_unit_window_lower hC hR
  have hs : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (zero_lt_one.trans_le hR))
  have hs' : Real.sqrt (R : ℝ) ≤ Real.sqrt (T : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show R ≤ T from tsub_le_self))
  calc
    _ ≤ unitWindowSeed * (killedGaussianConstant / (Real.sqrt (R : ℝ)) ^ 3) := by
      unfold centeredWindowConstant
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left killedGaussianConstant_pos.le
        (pow_pos hs _) (pow_le_pow_left₀ hs.le hs' _)) unitWindowSeed_pos.le
    _ ≤ P.real (A ∩ G) := by
      rw [hAG, hA]
      exact mul_le_mul_of_nonneg_left hbound unitWindowSeed_pos.le
    _ ≤ _ := measureReal_mono hSub

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

private noncomputable def bridgeFraction (t T : ℝ≥0) : ℝ := (t : ℝ) / (T : ℝ)

private noncomputable def continuousBridge (B : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω - bridgeFraction t T * B T ω

private lemma aemeasurable_continuousBridge (hB : IsPreBrownianReal B P) (T t : ℝ≥0) :
    AEMeasurable (continuousBridge B T t) P :=
  (hB.aemeasurable _).sub (aemeasurable_const.mul (hB.aemeasurable _))

private lemma indepFun_continuousBridge_endpoint (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    (hT : T ≠ 0) {t : ℕ → ℝ≥0} (ht : ∀ k, t k ≤ T) :
    IndepFun (fun ω k => continuousBridge B T (t k) ω) (B T) P := by
  let Y : Unit → Ω → ℝ := fun _ => B T
  have hJoint : IsGaussianProcess (Sum.elim (fun k => continuousBridge B T (t k)) Y) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    intro i
    cases i with
    | inl j =>
      refine ⟨{t j, T},
        { toFun v := v ⟨t j, by simp⟩ - bridgeFraction (t j) T * v ⟨T, by simp⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }, fun _ => rfl⟩
    | inr u =>
      exact ⟨{T},
        { toFun v := v ⟨T, by simp⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }, fun _ => rfl⟩
  have hIndep := hJoint.indepFun_of_covariance_eq_zero
    (fun j => aemeasurable_continuousBridge hB T (t j)) (fun _ => hB.aemeasurable _)
    (fun j _ => by
      have hne : (T : ℝ) ≠ 0 := by exact_mod_cast hT
      change cov[fun ω => B (t j) ω - bridgeFraction (t j) T * B T ω, B T; P] = 0
      rw [covariance_fun_sub_left, covariance_const_mul_left, hB.covariance_eval,
        hB.covariance_eval, min_eq_left (ht j), min_self]
      · unfold bridgeFraction
        field_simp
        <;> ring
      all_goals
        first
        | exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
        | exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _)
  exact hIndep.comp measurable_id (measurable_pi_apply ())

private lemma driftedPath_continuous (hB : IsBrownianReal B P) (d : ℝ) :
    ∀ᵐ ω ∂P, Continuous (driftedPath B d · ω) :=
  hB.cont.mono (fun _ h => h.sub (continuous_const.mul NNReal.continuous_coe))

private lemma continuous_window_drift_weight (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 1 ≤ T)
    {d : ℝ} (hd : 0 ≤ d) :
    driftWeight (-d) T 3 * P (closedWindow B 1 T (1 / 2) 1 3) ≤
      P (closedWindow (driftedPath B d) 1 T (1 / 2) 1 3) := by
  letI : Nonempty (Icc (1 : ℝ≥0) T) := ⟨⟨1, mem_Icc.mpr ⟨le_rfl, hT⟩⟩⟩
  let times := TopologicalSpace.denseSeq (Icc (1 : ℝ≥0) T)
  let t (k : ℕ) := (times k).val
  let V (ω : Ω) (k : ℕ) := continuousBridge B T (t k) ω
  let X := B T
  let Xd := driftedPath B d T
  let A : Set ((ℕ → ℝ) × ℝ) :=
    {z | (∀ k, 1 / 2 ≤ z.1 k + bridgeFraction (t k) T * z.2) ∧ z.2 ∈ Icc 1 3}
  have hT0 : T ≠ 0 := (zero_lt_one.trans_le hT).ne'
  have hV : AEMeasurable V P :=
    aemeasurable_pi_lambda _ (fun k => aemeasurable_continuousBridge hB.toIsPreBrownianReal T (t k))
  have hX : AEMeasurable X P := hB.toIsPreBrownianReal.aemeasurable _
  have hXd : AEMeasurable Xd P := hX.sub aemeasurable_const
  have hA : MeasurableSet A := by
    rw [show A = (⋂ k, {z : (ℕ → ℝ) × ℝ |
        1 / 2 ≤ z.1 k + bridgeFraction (t k) T * z.2}) ∩ {z | z.2 ∈ Icc 1 3} by
          ext z
          simp [A]]
    exact (MeasurableSet.iInter fun k => measurableSet_le measurable_const
      (((measurable_pi_apply k).comp measurable_fst).add
        (measurable_const.mul measurable_snd))).inter (measurable_snd measurableSet_Icc)
  have hIndep : IndepFun V X P := indepFun_continuousBridge_endpoint
    hB.toIsPreBrownianReal hT0 (fun k => (times k).property.2)
  have hIndepD : IndepFun V Xd P :=
    hIndep.comp measurable_id (measurable_id.sub_const (d * (T : ℝ)))
  have hXlaw : HasLaw X (gaussianReal 0 T) P := hB.toIsPreBrownianReal.hasLaw_eval T
  have hXdlaw : HasLaw Xd (gaussianReal (-d * (T : ℝ)) T) P := by
    have heq : Xd = fun ω => X ω + -(d * (T : ℝ)) := funext fun _ => sub_eq_add_neg _ _
    rw [heq]
    simpa only [zero_add, neg_mul] using gaussianReal_add_const hXlaw (-(d * (T : ℝ)))
  have hMap : P.map (fun ω => (V ω, X ω)) = (P.map V).prod (gaussianReal 0 T) := by
    rw [hIndep.map_prod_eq_prod_map_map hV hX, hXlaw.map_eq]
  have hMapD : P.map (fun ω => (V ω, Xd ω)) = (P.map V).prod (gaussianReal (-d * (T : ℝ)) T) := by
    rw [hIndepD.map_prod_eq_prod_map_map hV hXd, hXdlaw.map_eq]
  have hPre : (fun ω => (V ω, X ω)) ⁻¹' A =
      (fun ω t => B t ω) ⁻¹' closedWindowCyl t T (1 / 2) 1 3 := by
    ext ω
    simp [A, V, X, continuousBridge, closedWindowCyl]
  have hCancel (k : ℕ) (ω : Ω) : V ω k + bridgeFraction (t k) T * Xd ω = driftedPath B d (t k) ω := by
    have hne : (T : ℝ) ≠ 0 := by exact_mod_cast hT0
    simp only [V, continuousBridge, bridgeFraction, Xd, driftedPath]
    field_simp
    <;> ring
  have hPreD : (fun ω => (V ω, Xd ω)) ⁻¹' A =
      (fun ω t => driftedPath B d t ω) ⁻¹' closedWindowCyl t T (1 / 2) 1 3 := by
    ext ω
    change ((∀ k, 1 / 2 ≤ V ω k + bridgeFraction (t k) T * Xd ω) ∧ Xd ω ∈ Icc 1 3) ↔ _
    simp_rw [hCancel]
    rfl
  have hMain : (P.map V).prod (gaussianReal 0 T) A = P (closedWindow B 1 T (1 / 2) 1 3) := by
    rw [← hMap, Measure.map_apply_of_aemeasurable (hV.prodMk hX) hA, hPre]
    exact (measure_congr (closedWindow_ae_eq_dense times (TopologicalSpace.denseRange_denseSeq _)
      hB.cont (1 / 2) 1 3)).symm
  have hDrift : (P.map V).prod (gaussianReal (-d * (T : ℝ)) T) A =
      P (closedWindow (driftedPath B d) 1 T (1 / 2) 1 3) := by
    rw [← hMapD, Measure.map_apply_of_aemeasurable (hV.prodMk hXd) hA, hPreD]
    exact (measure_congr (closedWindow_ae_eq_dense times (TopologicalSpace.denseRange_denseSeq _)
      (driftedPath_continuous hB d) (1 / 2) 1 3)).symm
  have hbound := (negGaussian_product_window (P.map V) hA hd (fun _ hz => hz.2) hT0).1
  rw [hMain, hDrift] at hbound
  exact hbound

noncomputable def driftWindowConstant (d : ℝ) : ℝ :=
  centeredWindowConstant * Real.exp (-(3 * d))

lemma driftWindowConstant_pos (d : ℝ) : 0 < driftWindowConstant d :=
  mul_pos centeredWindowConstant_pos (Real.exp_pos _)

theorem continuous_drift_window_lower (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 2 ≤ T)
    {d : ℝ} (hd : 0 ≤ d) :
    driftWindowConstant d * Real.exp (-(d ^ 2 * (T : ℝ) / 2)) / (Real.sqrt (T : ℝ)) ^ 3 ≤
      P.real (closedWindow (driftedPath B d) 1 T (1 / 2) 1 3) := by
  have h1 : 1 ≤ T := (by norm_num : (1 : ℝ≥0) ≤ 2).trans hT
  have hL := continuous_window_drift_weight hB h1 hd
  have hLR := ENNReal.toReal_mono (measure_ne_top P _) hL
  rw [ENNReal.toReal_mul, driftWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hLR
  have he : Real.exp (-d * 3 - (-d) ^ 2 * (T : ℝ) / 2) =
      Real.exp (-(3 * d)) * Real.exp (-(d ^ 2 * (T : ℝ) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hLR
  have hc := centered_window_lower hB hT
  unfold Measure.real at hc ⊢
  have hm := mul_le_mul_of_nonneg_left hc
    (mul_nonneg (Real.exp_nonneg (-(3 * d))) (Real.exp_nonneg (-(d ^ 2 * (T : ℝ) / 2))))
  refine le_trans ?_ (hm.trans hLR)
  unfold driftWindowConstant
  ring_nf
  rfl

theorem brownian_reversePrefix (hB : IsBrownianReal B P) (T : ℝ≥0) :
    IsBrownianReal (reversePrefix B T) P where
  toIsPreBrownianReal := preBrownian_reversePrefix hB.toIsPreBrownianReal T
  cont := by
    filter_upwards [hB.cont] with ω h
    unfold reversePrefix
    exact (h.comp (continuous_const.max continuous_id)).sub
      (h.comp (continuous_sub_left T))

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B C : ℝ≥0 → Ω → ℝ}

/-- A time whose height beats the other arm and this arm through the preceding unit. -/
def armFavorable (B C : ℝ≥0 → Ω → ℝ) (d : ℝ) (T : ℝ≥0) : Set Ω :=
  closedWindow (driftedPath (reversePrefix B T) d) 1 T (1 / 2) 1 3 ∩ (riseAbove C d (1 / 2))ᶜ

private lemma armFavorable_measure_eq_mul (hB : IsBrownianReal B P)
    (hC : IsBrownianReal C P) (hBC : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    {T : ℝ≥0} (hT : 1 ≤ T) (d : ℝ) :
    P.real (armFavorable B C d T) =
      P.real (closedWindow (driftedPath (reversePrefix B T) d) 1 T (1 / 2) 1 3) *
        P.real (riseAbove C d (1 / 2))ᶜ := by
  letI : Nonempty (Icc (1 : ℝ≥0) T) := ⟨⟨1, mem_Icc.mpr ⟨le_rfl, hT⟩⟩⟩
  let times := TopologicalSpace.denseSeq (Icc (1 : ℝ≥0) T)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let G := closedWindowCyl (fun k => (times k).val) T (1 / 2) 1 3
  let R := riseCyl S d (1 / 2)
  let X (ω : Ω) (t : ℝ≥0) := driftedPath (reversePrefix B T) d t ω
  let Y (ω : Ω) (t : ℝ≥0) := C t ω
  let F (x : ℝ≥0 → ℝ) (t : ℝ≥0) := x (max T t) - x (T - t) - d * (t : ℝ)
  let E := closedWindow (driftedPath (reversePrefix B T) d) 1 T (1 / 2) 1 3
  let H := riseAbove C d (1 / 2)
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro t
    change Measurable (fun x : ℝ≥0 → ℝ => x (max T t) - x (T - t) - d * (t : ℝ))
    fun_prop
  have hI : IndepFun X Y P := hBC.comp hF measurable_id
  have hG : MeasurableSet G := closedWindowCyl_meas _ _ _ _ _
  have hR : MeasurableSet R := riseCyl_meas hSc _ _
  have hEae : E =ᵐ[P] X ⁻¹' G :=
    closedWindow_ae_eq_dense times (TopologicalSpace.denseRange_denseSeq _)
      (driftedPath_continuous (brownian_reversePrefix hB T) d) (1 / 2) 1 3
  have hHae : Hᶜ =ᵐ[P] Y ⁻¹' Rᶜ := by
    filter_upwards [riseAbove_ae_eq_dense hC hSd d (1 / 2)] with ω hω
    exact congrArg Not hω
  have hBoth : (armFavorable B C d T : Set Ω) =ᵐ[P] ((X ⁻¹' G ∩ Y ⁻¹' Rᶜ) : Set Ω) := by
    filter_upwards [hEae, hHae] with ω hω hω'
    exact congrArg₂ And hω hω'
  change P.real (armFavorable B C d T) = P.real E * P.real Hᶜ
  unfold Measure.real
  rw [measure_congr hBoth, hI.measure_inter_preimage_eq_mul G Rᶜ hG hR.compl, ENNReal.toReal_mul]
  exact congrArg₂ (fun a b : ℝ≥0∞ => a.toReal * b.toReal)
    (measure_congr hEae).symm (measure_congr hHae).symm

noncomputable def armTailConstant (d : ℝ) : ℝ :=
  driftWindowConstant d * (1 - Real.exp (-d))

lemma armTailConstant_pos {d : ℝ} (hd : 0 < d) : 0 < armTailConstant d := by
  apply mul_pos (driftWindowConstant_pos d)
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd))

theorem armFavorable_lower (hB : IsBrownianReal B P)
    (hC : IsBrownianReal C P) (hBC : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    {T : ℝ≥0} (hT : 2 ≤ T) {d : ℝ} (hd : 0 < d) :
    armTailConstant d * Real.exp (-(d ^ 2 * (T : ℝ) / 2)) / (Real.sqrt (T : ℝ)) ^ 3 ≤
      P.real (armFavorable B C d T) := by
  let H := riseAbove C d (1 / 2)
  have h1 : 1 ≤ T := (by norm_num : (1 : ℝ≥0) ≤ 2).trans hT
  rw [armFavorable_measure_eq_mul hB hC hBC h1]
  have hL := continuous_drift_window_lower (brownian_reversePrefix hB T) hT hd.le
  have hU := continuous_rise_upper hC hd (1 / 2)
  have hU' : P H ≤ ENNReal.ofReal (Real.exp (-d)) := by
    convert hU using 3 <;> ring
  have hUR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU'
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hUR
  change P.real H ≤ Real.exp (-d) at hUR
  have hCpl := measureReal_union_le (μ := P) H Hᶜ
  rw [union_compl_self, probReal_univ] at hCpl
  have hNR : 1 - Real.exp (-d) ≤ P.real Hᶜ := by linarith
  have hNP : 0 ≤ 1 - Real.exp (-d) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd.le))
  have hPos := driftWindowConstant_pos d
  have hprod := mul_le_mul hL hNR hNP (measureReal_nonneg (μ := P))
  refine le_trans ?_ hprod
  unfold armTailConstant
  ring_nf
  rfl

lemma armFavorable_lt_same {T : ℝ≥0} {d : ℝ} {ω : Ω}
    (hω : ω ∈ armFavorable B C d T) {t : ℝ≥0} (ht : t + 1 ≤ T) :
    driftedPath B d t ω < driftedPath B d T ω := by
  have hle : t ≤ T := (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ 1)).trans ht
  have hs : T - t ∈ Icc (1 : ℝ≥0) T :=
    ⟨le_tsub_of_add_le_right (by simpa only [add_comm] using ht), tsub_le_self⟩
  have h := hω.1.1 _ hs
  rw [drifted_reversePrefix_eq_sub B d hs.2 ω, tsub_tsub_cancel_of_le hle] at h
  linarith

lemma armFavorable_lt_other {T : ℝ≥0} {d : ℝ} {ω : Ω}
    (hω : ω ∈ armFavorable B C d T) (hzero : B 0 ω = 0) (t : ℝ≥0) :
    driftedPath C d t ω < driftedPath B d T ω := by
  have hH : ¬ ∃ s, (1 / 2 : ℝ) < driftedPath C d s ω := hω.2
  have hsmall : driftedPath C d t ω ≤ 1 / 2 := le_of_not_gt fun ht => hH ⟨t, ht⟩
  have hT := hω.1.2.1
  rw [drifted_reversePrefix_eq_sub B d le_rfl ω, tsub_self] at hT
  simp only [driftedPath, hzero, NNReal.coe_zero, mul_zero, sub_zero] at hT
  change _ < B T ω - d * ↑T
  linarith

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

private def smallGapCyl (n : ℕ) (d y : ℝ) : Set (Set.Iic (n : ℝ≥0) → ℝ) :=
  {f | ∀ j : Fin (n + 1),
    f ⟨(n : ℝ≥0) - (j.val : ℝ≥0), mem_Iic.mpr tsub_le_self⟩ -
      d * (((n : ℝ≥0) - (j.val : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ f ⟨n, mem_Iic.mpr le_rfl⟩ - d * (n : ℝ) + y}

private def smallGap (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (d y : ℝ) : Set Ω :=
  pastProjection B (n : ℝ≥0) ⁻¹' smallGapCyl n d y

private lemma smallGap_mem {n : ℕ} {d y : ℝ} {ω : Ω} :
    ω ∈ smallGap B n d y ↔ ∀ j : Fin (n + 1),
      driftedPath B d ((n : ℝ≥0) - (j.val : ℝ≥0)) ω ≤ driftedPath B d (n : ℝ≥0) ω + y := by
  simp only [smallGap, mem_preimage, smallGapCyl, mem_ofPred_eq, pastProjection,
    driftedPath, NNReal.coe_natCast]

private lemma smallGapCyl_meas (n : ℕ) (d y : ℝ) : MeasurableSet (smallGapCyl n d y) := by
  rw [show smallGapCyl n d y = ⋂ j : Fin (n + 1), {f : Set.Iic (n : ℝ≥0) → ℝ |
    f ⟨(n : ℝ≥0) - (j.val : ℝ≥0), mem_Iic.mpr tsub_le_self⟩ -
      d * (((n : ℝ≥0) - (j.val : ℝ≥0) : ℝ≥0) : ℝ)
      ≤ f ⟨n, mem_Iic.mpr le_rfl⟩ - d * (n : ℝ) + y} by ext f; simp [smallGapCyl]]
  exact MeasurableSet.iInter fun _ =>
    measurableSet_le ((measurable_pi_apply _).sub_const _) (((measurable_pi_apply _).sub_const _).add_const _)

private lemma smallGap_eq_reverse (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (d y : ℝ) :
    smallGap B n d y = survives (driftedPath (reversePrefix B (n : ℝ≥0)) d) n y := by
  ext ω
  rw [smallGap_mem]
  change _ ↔ ∀ j : Fin (n + 1), -y ≤ driftedPath (reversePrefix B (n : ℝ≥0)) d (j.val : ℝ≥0) ω
  apply forall_congr'
  intro j
  have hj : (j.val : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast (show j.val ≤ n by omega)
  rw [drifted_reversePrefix_eq_sub B d hj ω]
  constructor <;> intro h <;> linarith

private lemma drifted_future_increment (B : ℝ≥0 → Ω → ℝ) (d : ℝ)
    {s t : ℝ≥0} (h : s ≤ t) (ω : Ω) :
    driftedPath (shiftAfter B s) d (t - s) ω =
      driftedPath B d t ω - driftedPath B d s ω := by
  have ht : s + (t - s) = t := by rw [add_comm, tsub_add_cancel_of_le h]
  simp only [driftedPath, shiftAfter, ht, NNReal.coe_sub h]
  ring

def laterDominatesGrid (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ t : ℝ≥0, (n : ℝ≥0) ≤ t ∧
    ∀ j : Fin (n + 1), driftedPath B d (j.val : ℝ≥0) ω ≤ driftedPath B d t ω}

private lemma laterDominatesGrid_cover (B : ℝ≥0 → Ω → ℝ) (d : ℝ) (n : ℕ) :
    laterDominatesGrid B d n ⊆ ⋃ k : ℕ,
      smallGap B n d ((k : ℝ) + 1) ∩ riseAbove (shiftAfter B (n : ℝ≥0)) d ((k : ℝ) - 1) := by
  classical
  intro ω hω
  obtain ⟨t, ht, htd⟩ := hω
  let v (j : Fin (n + 1)) := driftedPath B d ((n : ℝ≥0) - (j.val : ℝ≥0)) ω -
    driftedPath B d (n : ℝ≥0) ω
  let G : ℝ := Finset.univ.sup' Finset.univ_nonempty v
  have hG (j : Fin (n + 1)) : v j ≤ G := Finset.le_sup' v (Finset.mem_univ j)
  have h0 : 0 ≤ G := by simpa [v] using hG (0 : Fin (n + 1))
  let k := ⌊G⌋₊
  have hk₁ : (k : ℝ) ≤ G := Nat.floor_le h0
  have hk₂ : G < (k : ℝ) + 1 := Nat.lt_floor_add_one G
  apply mem_iUnion.mpr
  refine ⟨k, smallGap_mem.mpr ?_, ?_⟩
  · intro j
    have h := (hG j).trans hk₂.le
    dsimp [v] at h
    linarith
  · refine ⟨t - (n : ℝ≥0), ?_⟩
    rw [drifted_future_increment B d ht ω]
    have hG' : G ≤ driftedPath B d t ω - driftedPath B d (n : ℝ≥0) ω := by
      apply Finset.sup'_le
      intro j _
      have hj : j.val ≤ n := by omega
      let i : Fin (n + 1) := ⟨n - j.val, by omega⟩
      exact sub_le_sub_right (by simpa [i, natCast_sub_nnreal hj] using htd i) _
    linarith [hk₁.trans hG']

private lemma measure_gap_and_rise (hB : IsBrownianReal B P) (n : ℕ) (d y z : ℝ) :
    P (smallGap B n d y ∩ riseAbove (shiftAfter B (n : ℝ≥0)) d z) =
      P (smallGap B n d y) * P (riseAbove (shiftAfter B (n : ℝ≥0)) d z) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let C (ω : Ω) (t : ℝ≥0) := shiftAfter B (n : ℝ≥0) t ω
  have hC : IsBrownianReal (shiftAfter B (n : ℝ≥0)) P := hB.shift _
  have hAE := riseAbove_ae_eq_dense hC hSd d z
  have hinter : ((smallGap B n d y ∩ riseAbove (shiftAfter B (n : ℝ≥0)) d z) : Set Ω) =ᵐ[P]
      ((smallGap B n d y ∩ (C ⁻¹' riseCyl S d z)) : Set Ω) := by
    filter_upwards [hAE] with ω hω
    change (_ ∧ ω ∈ riseAbove _ d z) = (_ ∧ ω ∈ C ⁻¹' riseCyl S d z)
    exact congrArg (fun p : Prop => (ω ∈ smallGap B n d y) ∧ p) hω
  have hIndep : IndepFun (pastProjection B (n : ℝ≥0)) C P :=
    (hB.toIsPreBrownianReal.indepFun_shift (n : ℝ≥0)).symm
  rw [measure_congr hinter, smallGap, hIndep.measure_inter_preimage_eq_mul _ _
    (smallGapCyl_meas n d y) (riseCyl_meas hSc d z)]
  rw [measure_congr hAE]

noncomputable def continuousTailConstant (d : ℝ) : ℝ :=
  2 * driftSurvivalConstant d * Real.exp (3 * d) * (∑' k, tailSeriesTerm d k)

theorem laterDominatesGrid_upper (hB : IsBrownianReal B P) {n : ℕ} (hn : 1 ≤ n) {d : ℝ} (hd : 0 < d) :
    P.real (laterDominatesGrid B d n) ≤ continuousTailConstant d * Real.exp (-(d ^ 2 * (n : ℝ) / 2)) /
      (Real.sqrt ((n : ℝ) + 1)) ^ 3 := by
  let U := 2 * driftSurvivalConstant d * Real.exp (3 * d) *
    Real.exp (-(d ^ 2 * (n : ℝ) / 2)) / (Real.sqrt ((n : ℝ) + 1)) ^ 3
  let E (k : ℕ) := smallGap B n d ((k : ℝ) + 1) ∩ riseAbove (shiftAfter B (n : ℝ≥0)) d ((k : ℝ) - 1)
  have hC := driftSurvivalConstant_pos hd
  have hU : 0 ≤ U := by unfold U; positivity
  have hEach (k : ℕ) : P (E k) ≤ ENNReal.ofReal (U * tailSeriesTerm d k) := by
    let y := (k : ℝ) + 1
    let z := (k : ℝ) - 1
    let L := driftSurvivalConstant d * (1 + y) * Real.exp (d * y - d ^ 2 * (n : ℝ) / 2) /
      (Real.sqrt ((n : ℝ) + 1)) ^ 3
    have hL : 0 ≤ L := by unfold L y; positivity
    have hG : P (smallGap B n d y) ≤ ENNReal.ofReal L := by
      apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).1
      rw [ENNReal.toReal_ofReal hL, smallGap_eq_reverse]
      exact drifted_survival_upper (preBrownian_reversePrefix hB.toIsPreBrownianReal _) hn hd
        (by unfold y; positivity)
    have hF := continuous_rise_upper (show IsBrownianReal (shiftAfter B (n : ℝ≥0)) P from hB.shift _) hd z
    change P (smallGap B n d y ∩ riseAbove (shiftAfter B (n : ℝ≥0)) d z) ≤ _
    rw [measure_gap_and_rise hB]
    calc
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (Real.exp (-(2 * d * z))) := by gcongr
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hL]
        apply ENNReal.ofReal_le_ofReal
        have hExp : Real.exp (d * y - d ^ 2 * (n : ℝ) / 2) * Real.exp (-(2 * d * z)) =
            Real.exp (3 * d) * Real.exp (-(d ^ 2 * (n : ℝ) / 2)) * Real.exp (-d * (k : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          unfold y z
          ring
        have hlin : (1 + y) ≤ 2 * (1 + (k : ℝ)) := by unfold y; linarith [Nat.cast_nonneg (α := ℝ) k]
        have hprod := mul_le_mul_of_nonneg_right hlin
          (show 0 ≤ driftSurvivalConstant d * Real.exp (3 * d) *
            Real.exp (-(d ^ 2 * (n : ℝ) / 2)) * Real.exp (-d * (k : ℝ)) /
              (Real.sqrt ((n : ℝ) + 1)) ^ 3 by positivity)
        unfold L U tailSeriesTerm
        rw [show driftSurvivalConstant d * (1 + y) * Real.exp (d * y - d ^ 2 * (n : ℝ) / 2) /
              (Real.sqrt ((n : ℝ) + 1)) ^ 3 * Real.exp (-(2 * d * z)) =
            (1 + y) * (driftSurvivalConstant d *
              (Real.exp (d * y - d ^ 2 * (n : ℝ) / 2) * Real.exp (-(2 * d * z))) /
              (Real.sqrt ((n : ℝ) + 1)) ^ 3) by ring, hExp]
        convert hprod using 1 <;> first | rfl | ring
  have hSummable : Summable (fun k => U * tailSeriesTerm d k) := (summable_tailSeriesTerm hd).mul_left U
  have hM : P (laterDominatesGrid B d n) ≤ ENNReal.ofReal (U * ∑' k, tailSeriesTerm d k) := by
    calc
      _ ≤ P (⋃ k : ℕ, E k) := measure_mono (laterDominatesGrid_cover B d n)
      _ ≤ ∑' k, P (E k) := measure_iUnion_le _
      _ ≤ ∑' k, ENNReal.ofReal (U * tailSeriesTerm d k) := ENNReal.tsum_le_tsum hEach
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hU (tailSeriesTerm_nonneg d k)) hSummable,
          (summable_tailSeriesTerm hd).tsum_mul_left]
  have hNonneg : 0 ≤ U * ∑' k, tailSeriesTerm d k := mul_nonneg hU (tsum_nonneg (tailSeriesTerm_nonneg d))
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM
  rw [ENNReal.toReal_ofReal hNonneg] at hReal
  refine hReal.trans_eq ?_
  unfold U continuousTailConstant
  ring

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

noncomputable def decay (d x : ℝ) : ℝ := Real.exp (-(d ^ 2 * x / 2))

lemma decay_pos (d x : ℝ) : 0 < decay d x := Real.exp_pos _

private lemma decay_add (d x y : ℝ) : decay d (x + y) = decay d x * decay d y := by
  unfold decay
  rw [← Real.exp_add]
  congr 1
  ring

private lemma decay_antitone (d : ℝ) : Antitone (decay d) := by
  intro x y hxy
  apply Real.exp_le_exp.mpr
  linarith [mul_le_mul_of_nonneg_left hxy (sq_nonneg d)]

private lemma decay_lt_one {d x : ℝ} (hd : 0 < d) (hx : 0 < x) : decay d x < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact neg_neg_of_pos (div_pos (mul_pos (pow_pos hd _) hx) (by norm_num))

private lemma decay_nat_mul (d x : ℝ) (n : ℕ) : decay d ((n : ℝ) * x) = decay d x ^ n := by
  unfold decay
  rw [← Real.exp_nat_mul]
  congr 1
  ring

noncomputable def tailScale (d x : ℝ) : ℝ := decay d x / (Real.sqrt (x + 1)) ^ 3

lemma tailScale_pos (d : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 < tailScale d x :=
  div_pos (decay_pos d x) (pow_pos (Real.sqrt_pos.mpr (by linarith)) _)

private lemma tailScale_shift_le (d : ℝ) {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) :
    tailScale d (x + b) ≤ decay d b * tailScale d x := by
  have h := Real.sqrt_le_sqrt (show x + 1 ≤ (x + b) + 1 by linarith)
  unfold tailScale
  rw [add_comm x b, decay_add, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (decay_pos d b).le
  apply div_le_div_of_nonneg_left (decay_pos d x).le
  · exact pow_pos (Real.sqrt_pos.mpr (by linarith)) _
  · rw [add_comm b x]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h _

private lemma tailScale_floor_upper (d : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    tailScale d (⌊x⌋₊ : ℝ) ≤ (8 * decay d (-1)) * tailScale d x := by
  let n : ℝ := (⌊x⌋₊ : ℕ)
  have hn0 : 0 ≤ n := by unfold n; positivity
  have hn1 : 1 ≤ n := by
    have h : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ x)).2 (by simpa using hx)
    change (1 : ℝ) ≤ (⌊x⌋₊ : ℝ)
    exact_mod_cast h
  have hn : x - 1 ≤ n := by linarith [Nat.lt_floor_add_one x]
  have hExp : decay d n ≤ decay d (-1) * decay d x := by
    rw [← decay_add]
    exact decay_antitone d (by linarith)
  have hD : Real.sqrt (x + 1) ≤ 2 * Real.sqrt (n + 1) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ n + 1)]
      nlinarith
  have hD' : (Real.sqrt (x + 1)) ^ 3 ≤ 8 * (Real.sqrt (n + 1)) ^ 3 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hD 3
    calc
      _ ≤ (2 * Real.sqrt (n + 1)) ^ 3 := h
      _ = _ := by ring
  have hp : 0 < (Real.sqrt (n + 1)) ^ 3 := by positivity
  have hq : 0 < (Real.sqrt (x + 1)) ^ 3 := by
    exact pow_pos (Real.sqrt_pos.mpr (by linarith)) _
  change decay d n / (Real.sqrt (n + 1)) ^ 3 ≤ (8 * decay d (-1)) *
    (decay d x / (Real.sqrt (x + 1)) ^ 3)
  rw [← mul_div_assoc, div_le_div_iff₀ hp hq]
  calc
    _ ≤ (decay d (-1) * decay d x) * (8 * (Real.sqrt (n + 1)) ^ 3) :=
      mul_le_mul hExp hD' hq.le (mul_nonneg (decay_pos _ _).le (decay_pos _ _).le)
    _ = _ := by ring

private lemma tailScale_ceil_lower (d : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (decay d 2 / 8) * tailScale d x ≤
      decay d ((⌊x⌋₊ : ℝ) + 2) / (Real.sqrt ((⌊x⌋₊ : ℝ) + 2)) ^ 3 := by
  let n : ℝ := (⌊x⌋₊ : ℕ) + 2
  have hn : n ≤ x + 2 := by
    dsimp [n]
    linarith only [Nat.floor_le (by linarith : 0 ≤ x)]
  have hn0 : 0 < n := by unfold n; positivity
  have hExp : decay d 2 * decay d x ≤ decay d n := by
    rw [← decay_add, add_comm]
    exact decay_antitone d hn
  have hD : Real.sqrt n ≤ 2 * Real.sqrt (x + 1) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ x + 1)]
      nlinarith
  have hD' : (Real.sqrt n) ^ 3 ≤ 8 * (Real.sqrt (x + 1)) ^ 3 := by
    calc
      _ ≤ (2 * Real.sqrt (x + 1)) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hD _
      _ = _ := by ring
  have hp : 0 < (Real.sqrt (x + 1)) ^ 3 := pow_pos (Real.sqrt_pos.mpr (by linarith)) _
  have hq : 0 < (Real.sqrt n) ^ 3 := by positivity
  change (decay d 2 / 8) * (decay d x / (Real.sqrt (x + 1)) ^ 3) ≤ decay d n / (Real.sqrt n) ^ 3
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos (by norm_num) hp) hq]
  exact mul_le_mul hExp hD' hq.le (decay_pos _ _).le

noncomputable def latticeTailConstant (d : ℝ) : ℝ := driftSurvivalConstant d / (1 - decay d 1)

lemma latticeTailConstant_pos {d : ℝ} (hd : 0 < d) : 0 < latticeTailConstant d :=
  div_pos (driftSurvivalConstant_pos hd) (sub_pos.mpr (decay_lt_one hd zero_lt_one))

private lemma continuousTailConstant_pos {d : ℝ} (hd : 0 < d) : 0 < continuousTailConstant d := by
  have h := (summable_tailSeriesTerm hd).tsum_pos (tailSeriesTerm_nonneg d) 0
    (by unfold tailSeriesTerm; positivity)
  unfold continuousTailConstant
  exact mul_pos (mul_pos (mul_pos (by norm_num) (driftSurvivalConstant_pos hd)) (Real.exp_pos _)) h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem lattice_tail_upper (hB : IsPreBrownianReal B P) {m : ℕ} (hm : 1 ≤ m) {d : ℝ}
    (hd : 0 < d) :
    P.real (⋃ k : ℕ, latticeRecord B d (m + k)) ≤ latticeTailConstant d * tailScale d m := by
  let q := decay d 1
  let u := driftSurvivalConstant d * tailScale d m
  have hq₀ : 0 ≤ q := (decay_pos _ _).le
  have hq₁ : q < 1 := decay_lt_one hd zero_lt_one
  have hu : 0 ≤ u := mul_nonneg (driftSurvivalConstant_pos hd).le (tailScale_pos d (by positivity)).le
  have hs := summable_geometric_of_lt_one hq₀ hq₁
  have hEach (k : ℕ) : P (latticeRecord B d (m + k)) ≤ ENNReal.ofReal (u * q ^ k) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (mul_nonneg hu (pow_nonneg hq₀ _))]
    have h : P.real (latticeRecord B d (m + k)) ≤
        driftSurvivalConstant d * tailScale d ((m + k : ℕ) : ℝ) := by
      simpa only [tailScale, decay, mul_div_assoc] using latticeRecord_upper hB (n := m + k) (by omega) hd
    refine h.trans ?_
    have hshift := tailScale_shift_le d (x := (m : ℝ)) (b := (k : ℝ)) (by positivity) (by positivity)
    have hqk : decay d (k : ℝ) = q ^ k := by simpa only [q, mul_one] using decay_nat_mul d 1 k
    rw [hqk] at hshift
    have hb := mul_le_mul_of_nonneg_left hshift (driftSurvivalConstant_pos hd).le
    rw [Nat.cast_add]
    refine hb.trans_eq ?_
    unfold u
    ring
  have hM := (measure_iUnion_le (μ := P) (fun k : ℕ => latticeRecord B d (m + k))).trans
    (ENNReal.tsum_le_tsum hEach)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hu (pow_nonneg hq₀ k)) (hs.mul_left u),
    hs.tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁] at hM
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM
  rw [ENNReal.toReal_ofReal (mul_nonneg hu (inv_nonneg.mpr (sub_nonneg.mpr hq₁.le)))] at hR
  refine hR.trans_eq ?_
  unfold u q latticeTailConstant
  ring

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open OMA.S_mo_142880 (height)
open scoped NNReal ENNReal

noncomputable def latticeUpper (d : ℝ) : ℝ := latticeTailConstant d * (8 * decay d (-1))
noncomputable def continuousUpper (d : ℝ) : ℝ := continuousTailConstant d * (8 * decay d (-1))
noncomputable def argmaxLower (d : ℝ) : ℝ := armTailConstant d * (decay d 2 / 8)

private lemma latticeUpper_pos {d : ℝ} (hd : 0 < d) : 0 < latticeUpper d :=
  mul_pos (latticeTailConstant_pos hd) (mul_pos (by norm_num) (decay_pos _ _))

private lemma continuousUpper_pos {d : ℝ} (hd : 0 < d) : 0 < continuousUpper d :=
  mul_pos (continuousTailConstant_pos hd) (mul_pos (by norm_num) (decay_pos _ _))

private lemma argmaxLower_pos {d : ℝ} (hd : 0 < d) : 0 < argmaxLower d :=
  mul_pos (armTailConstant_pos hd) (div_pos (decay_pos _ _) (by norm_num))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

abbrev positiveArm (B : ℝ → Ω → ℝ) (t : ℝ≥0) := B (t : ℝ)
abbrev negativeArm (B : ℝ → Ω → ℝ) (t : ℝ≥0) := B (-(t : ℝ))

private lemma height_positive (B : ℝ → Ω → ℝ) (d : ℝ) (t : ℝ≥0) (ω : Ω) :
    height B d (t : ℝ) ω = driftedPath (positiveArm B) d t ω := by
  simp [height, driftedPath, abs_of_nonneg t.coe_nonneg]

private lemma height_negative (B : ℝ → Ω → ℝ) (d : ℝ) (t : ℝ≥0) (ω : Ω) :
    height B d (-(t : ℝ)) ω = driftedPath (negativeArm B) d t ω := by
  simp [height, driftedPath, abs_of_nonneg t.coe_nonneg]

private lemma real_measure_mono_ae {A E : Set Ω} (h : A ≤ᵐ[P] E) : P.real A ≤ P.real E :=
  ENNReal.toReal_mono (measure_ne_top P E) (measure_mono_ae h)

private lemma armFavorable_beats_height {B : ℝ → Ω → ℝ} {d : ℝ} {ω : Ω} {n : ℕ} {x z : ℝ}
    (hω : ω ∈ armFavorable (positiveArm B) (negativeArm B) d (n : ℝ≥0))
    (hzero : B 0 ω = 0) (hcut : x + 1 < (n : ℝ)) (hz : z ≤ x) :
    height B d z ω < height B d (n : ℝ) ω := by
  rw [← NNReal.coe_natCast, height_positive]
  by_cases hz0 : 0 ≤ z
  · let t : ℝ≥0 := ⟨z, hz0⟩
    have ht : t + 1 ≤ (n : ℝ≥0) := by
      norm_cast
      change z + 1 ≤ (n : ℝ)
      linarith
    change height B d (t : ℝ) ω < _
    rw [height_positive]
    exact armFavorable_lt_same hω ht
  · let t : ℝ≥0 := ⟨-z, by linarith⟩
    rw [show z = -(t : ℝ) by change z = - -z; ring, height_negative]
    exact armFavorable_lt_other hω hzero t

private lemma floor_at_least_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ ⌊x⌋₊ :=
  (Nat.le_floor_iff (by linarith : 0 ≤ x)).2 (by simpa using hx)

private lemma argmax_right_lower {B : ℝ → Ω → ℝ}
    (hB : IsBrownianReal (positiveArm B) P) (hC : IsBrownianReal (negativeArm B) P)
    (hBC : IndepFun (fun ω t => positiveArm B t ω) (fun ω t => negativeArm B t ω) P)
    {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 1 ≤ x) :
    argmaxLower d * tailScale d x ≤
        P.real (armFavorable (positiveArm B) (negativeArm B) d ((⌊x⌋₊ + 2 : ℕ) : ℝ≥0)) := by
  let n := ⌊x⌋₊ + 2
  have h2 : (2 : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast (show 2 ≤ n by omega)
  have h := armFavorable_lower hB hC hBC h2 hd
  simp only [NNReal.coe_natCast] at h
  refine le_trans ?_ h
  have hs := mul_le_mul_of_nonneg_left (tailScale_ceil_lower d hx) (armTailConstant_pos hd).le
  change (armTailConstant d * (decay d 2 / 8)) * tailScale d x ≤
    armTailConstant d * decay d (n : ℝ) / (Real.sqrt (n : ℝ)) ^ 3
  rw [show (n : ℝ) = (⌊x⌋₊ : ℝ) + 2 by simp [n]]
  simpa only [mul_assoc, mul_div_assoc] using hs

theorem lattice_argmax_right_lower {B : ℝ → Ω → ℝ}
    (hB : IsBrownianReal (positiveArm B) P) (hC : IsBrownianReal (negativeArm B) P)
    (hBC : IndepFun (fun ω t => positiveArm B t ω) (fun ω t => negativeArm B t ω) P)
    {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 1 ≤ x) {D : Ω → ℤ}
    (hD : ∀ᵐ ω ∂P, ∀ n : ℤ, height B d n ω ≤ height B d (D ω) ω) :
    argmaxLower d * tailScale d x ≤ P.real {ω | x < (D ω : ℝ)} := by
  let n := ⌊x⌋₊ + 2
  have hcut : x + 1 < (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith [Nat.lt_floor_add_one x]
  refine (argmax_right_lower hB hC hBC hd hx).trans (real_measure_mono_ae ?_)
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero, hD] with ω hzero hDω hω
  change x < (D ω : ℝ)
  by_contra! h
  have hlt := armFavorable_beats_height hω hzero hcut h
  exact (not_lt_of_ge (by simpa [n] using hDω (n : ℤ))) hlt

theorem continuous_argmax_right_lower {B : ℝ → Ω → ℝ}
    (hB : IsBrownianReal (positiveArm B) P) (hC : IsBrownianReal (negativeArm B) P)
    (hBC : IndepFun (fun ω t => positiveArm B t ω) (fun ω t => negativeArm B t ω) P)
    {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 1 ≤ x) {T : Ω → ℝ}
    (hT : ∀ᵐ ω ∂P, ∀ t : ℝ, height B d t ω ≤ height B d (T ω) ω) :
    argmaxLower d * tailScale d x ≤ P.real {ω | x < T ω} := by
  let n := ⌊x⌋₊ + 2
  have hcut : x + 1 < (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith [Nat.lt_floor_add_one x]
  refine (argmax_right_lower hB hC hBC hd hx).trans (real_measure_mono_ae ?_)
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero, hT] with ω hzero hTω hω
  change x < T ω
  by_contra! h
  exact (not_lt_of_ge (hTω (n : ℝ))) (armFavorable_beats_height hω hzero hcut h)

theorem lattice_argmax_right_upper {B : ℝ → Ω → ℝ}
    (hB : IsPreBrownianReal (positiveArm B) P) {d : ℝ} (hd : 0 < d)
    {x : ℝ} (hx : 1 ≤ x) {D : Ω → ℤ}
    (hD : ∀ᵐ ω ∂P, ∀ n : ℤ, height B d n ω ≤ height B d (D ω) ω) :
    P.real {ω | x ≤ (D ω : ℝ)} ≤ latticeUpper d * tailScale d x := by
  let m := ⌊x⌋₊
  have hM : ({ω | x ≤ (D ω : ℝ)} : Set Ω) ≤ᵐ[P]
      ((⋃ k : ℕ, latticeRecord (positiveArm B) d (m + k)) : Set Ω) := by
    filter_upwards [hD] with ω hDω hω
    change x ≤ (D ω : ℝ) at hω
    have hnonneg : (0 : ℝ) ≤ (D ω : ℝ) := by linarith
    let k := (D ω).toNat
    have hk : (k : ℤ) = D ω := Int.toNat_of_nonneg (by exact_mod_cast hnonneg)
    have hkR : (k : ℝ) = (D ω : ℝ) := by exact_mod_cast hk
    have hkm : m ≤ k := by
      have h : (m : ℝ) ≤ (k : ℝ) := by rw [hkR]; exact (Nat.floor_le (by linarith)).trans hω
      exact_mod_cast h
    apply mem_iUnion.mpr
    refine ⟨k - m, ?_⟩
    rw [show m + (k - m) = k by omega]
    intro j
    rw [← height_positive, ← height_positive, NNReal.coe_natCast, NNReal.coe_natCast, hkR]
    simpa using hDω (j.val : ℤ)
  refine (real_measure_mono_ae hM).trans ((lattice_tail_upper hB (floor_at_least_one hx) hd).trans ?_)
  have h := mul_le_mul_of_nonneg_left (tailScale_floor_upper d hx) (latticeTailConstant_pos hd).le
  simpa only [latticeUpper, mul_assoc] using h

theorem continuous_argmax_right_upper {B : ℝ → Ω → ℝ}
    (hB : IsBrownianReal (positiveArm B) P) {d : ℝ} (hd : 0 < d)
    {x : ℝ} (hx : 1 ≤ x) {T : Ω → ℝ}
    (hT : ∀ᵐ ω ∂P, ∀ t : ℝ, height B d t ω ≤ height B d (T ω) ω) :
    P.real {ω | x ≤ T ω} ≤ continuousUpper d * tailScale d x := by
  let m := ⌊x⌋₊
  have hM : ({ω | x ≤ T ω} : Set Ω) ≤ᵐ[P] (laterDominatesGrid (positiveArm B) d m : Set Ω) := by
    filter_upwards [hT] with ω hTω hω
    change x ≤ T ω at hω
    let t : ℝ≥0 := ⟨T ω, by linarith⟩
    have ht : (m : ℝ≥0) ≤ t := by exact_mod_cast (show (m : ℝ) ≤ T ω from
      (Nat.floor_le (by linarith)).trans hω)
    refine ⟨t, ht, ?_⟩
    intro j
    rw [← height_positive, ← height_positive, NNReal.coe_natCast]
    exact hTω _
  have hb : P.real (laterDominatesGrid (positiveArm B) d m) ≤
      continuousTailConstant d * tailScale d m := by
    simpa only [tailScale, decay, mul_div_assoc] using laterDominatesGrid_upper hB (floor_at_least_one hx) hd
  refine (real_measure_mono_ae hM).trans (hb.trans ?_)
  have h := mul_le_mul_of_nonneg_left (tailScale_floor_upper d hx) (continuousTailConstant_pos hd).le
  simpa only [continuousUpper, mul_assoc] using h

end GaussianWalkSurvival

namespace GaussianWalkSurvival

open MeasureTheory ProbabilityTheory Set Real
open OMA.S_mo_142880 (height)
open scoped NNReal ENNReal

private lemma tailScale_shift_le_of_le (d : ℝ) {w r y : ℝ} (hw : 0 ≤ w) (hr : 0 ≤ r)
    (hy : w + r ≤ y) : tailScale d y ≤ decay d r * tailScale d w := by
  have h := tailScale_shift_le d hw (show 0 ≤ y - w by linarith)
  rw [show w + (y - w) = y by ring] at h
  exact h.trans (mul_le_mul_of_nonneg_right (decay_antitone d (by linarith)) (tailScale_pos d hw).le)

private lemma exists_decay_le {d U L : ℝ} (hd : 0 < d) (hU : 0 < U) (hL : 0 < L) :
    ∃ r : ℝ, 0 ≤ r ∧ U * decay d r ≤ L := by
  let r := 2 * (U / L) / d ^ 2
  refine ⟨r, by unfold r; positivity, ?_⟩
  have hfactor : d ^ 2 * r / 2 = U / L := by
    unfold r
    have hd0 : d ≠ 0 := hd.ne'
    field_simp
  have hle : U / L ≤ Real.exp (U / L) := by
    linarith [Real.add_one_le_exp (U / L)]
  have hmul := (div_le_iff₀ hL).mp hle
  rw [decay, hfactor, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

private lemma tailUpper_shift {d U L r w y : ℝ} (hU : 0 ≤ U) (hr : 0 ≤ r)
    (hdecay : U * decay d r ≤ L) (hw : 0 ≤ w) (hy : w + r ≤ y) :
    U * tailScale d y ≤ L * tailScale d w := calc
  _ ≤ U * (decay d r * tailScale d w) :=
    mul_le_mul_of_nonneg_left (tailScale_shift_le_of_le d hw hr hy) hU
  _ = (U * decay d r) * tailScale d w := (mul_assoc ..).symm
  _ ≤ _ := mul_le_mul_of_nonneg_right hdecay (tailScale_pos d hw).le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Upper and lower tail estimates at the same rate give a uniform additive shift. -/
private lemma compare_from_tails {d U V L r : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hr : 0 ≤ r)
    (hUdecay : U * decay d r ≤ L) (hVdecay : V * decay d r ≤ L)
    {D T : Ω → ℝ} (hDM : AEMeasurable D P) (hTM : AEMeasurable T P)
    (hDR : ∀ y ≥ 1, P.real {ω | y ≤ D ω} ≤ U * tailScale d y)
    (hTR : ∀ y ≥ 1, L * tailScale d y ≤ P.real {ω | y < T ω})
    (hDL : ∀ y ≥ 1, L * tailScale d y ≤ P.real {ω | D ω ≤ -y})
    (hTL : ∀ y ≥ 1, P.real {ω | T ω ≤ -y} ≤ V * tailScale d y)
    (x : ℝ) : P {ω | x < D ω} ≤ P {ω | x < T ω + (2 * r + 2)} := by
  let b := 2 * r + 2
  change P {ω | x < D ω} ≤ P {ω | x < T ω + b}
  have hShift : {ω | x < T ω + b} = {ω | x - b < T ω} := by
    ext ω
    change (x < T ω + b) ↔ x - b < T ω
    exact sub_lt_iff_lt_add.symm
  rw [hShift]
  apply (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
  change P.real {ω | x < D ω} ≤ P.real {ω | x - b < T ω}
  by_cases hx : x ≤ r + 1
  · let w := max 1 (-x)
    have hw : 1 ≤ w := le_max_left _ _
    have hwx : -x ≤ w := le_max_right _ _
    have hwy : w + r ≤ b - x := by
      have h : w ≤ b - x - r := max_le (by dsimp [b]; linarith) (by dsimp [b]; linarith)
      linarith
    have hy : 1 ≤ b - x := by linarith
    have hLeft : P.real {ω | T ω ≤ x - b} ≤ P.real {ω | D ω ≤ x} := calc
      _ ≤ V * tailScale d (b - x) := by
        simpa only [neg_sub] using hTL (b - x) hy
      _ ≤ L * tailScale d w := tailUpper_shift hV hr hVdecay (by linarith) hwy
      _ ≤ P.real {ω | D ω ≤ -w} := hDL w hw
      _ ≤ _ := measureReal_mono (by
        intro ω hω
        change D ω ≤ -w at hω
        change D ω ≤ x
        linarith)
    have hDc : ({ω | x < D ω} : Set Ω)ᶜ = {ω | D ω ≤ x} := by ext ω; simp
    have hTc : ({ω | x - b < T ω} : Set Ω)ᶜ = {ω | T ω ≤ x - b} := by ext ω; simp
    have hDn : NullMeasurableSet {ω | x < D ω} P :=
      hDM.nullMeasurableSet_preimage measurableSet_Ioi
    have hTn : NullMeasurableSet {ω | x - b < T ω} P :=
      hTM.nullMeasurableSet_preimage measurableSet_Ioi
    rw [← hDc, ← hTc, measureReal_compl₀ hTn, measureReal_compl₀ hDn] at hLeft
    linarith
  · let w := max 1 (x - b)
    have hw : 1 ≤ w := le_max_left _ _
    have hwx : x - b ≤ w := le_max_right _ _
    have hwy : w + r ≤ x := by
      have h : w ≤ x - r := max_le (by linarith) (by dsimp [b]; linarith)
      linarith
    have hy : 1 ≤ x := by linarith
    calc
      _ ≤ P.real {ω | x ≤ D ω} := measureReal_mono (by
        intro ω hω
        change x < D ω at hω
        exact hω.le)
      _ ≤ U * tailScale d x := hDR x hy
      _ ≤ L * tailScale d w := tailUpper_shift hU hr hUdecay (by linarith) hwy
      _ ≤ P.real {ω | w < T ω} := hTR w hw
      _ ≤ _ := measureReal_mono (by
        intro ω hω
        change w < T ω at hω
        exact lt_of_le_of_lt hwx hω)

private lemma height_reflect (B : ℝ → Ω → ℝ) (d t : ℝ) (ω : Ω) :
    height (fun s => B (-s)) d t ω = height B d (-t) ω := by simp [height]

theorem brownianArgmaxShift (d : ℝ) (hd : 0 < d) :
    ∃ b : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
      IsBrownianReal (positiveArm B) P → IsBrownianReal (negativeArm B) P →
      IndepFun (fun ω t => positiveArm B t ω) (fun ω t => negativeArm B t ω) P →
      ∀ (D : Ω → ℤ) (T : Ω → ℝ), AEMeasurable D P → AEMeasurable T P →
      (∀ᵐ ω ∂P, ∀ n : ℤ, height B d n ω ≤ height B d (D ω) ω) →
      (∀ᵐ ω ∂P, ∀ t : ℝ, height B d t ω ≤ height B d (T ω) ω) →
      ∀ x : ℝ, P {ω | x < (D ω : ℝ)} ≤ P {ω | x < T ω + b} := by
  let U := latticeUpper d
  let V := continuousUpper d
  let L := argmaxLower d
  have hU : 0 < U := latticeUpper_pos hd
  have hV : 0 < V := continuousUpper_pos hd
  have hL : 0 < L := argmaxLower_pos hd
  obtain ⟨r, hr, hdecay⟩ := exists_decay_le hd (add_pos hU hV) hL
  refine ⟨2 * r + 2, ?_⟩
  intro Ω mΩ P hP B hB hC hBC D T hDM hTM hD hT x
  have hDR : ∀ y ≥ 1, P.real {ω | y ≤ (D ω : ℝ)} ≤ U * tailScale d y :=
    fun _ hy => lattice_argmax_right_upper hB.toIsPreBrownianReal hd hy hD
  have hTR : ∀ y ≥ 1, L * tailScale d y ≤ P.real {ω | y < T ω} :=
    fun _ hy => continuous_argmax_right_lower hB hC hBC hd hy hT
  let Br (s : ℝ) := B (-s)
  have hBrev : IsBrownianReal (positiveArm Br) P := hC
  have hCrev : IsBrownianReal (negativeArm Br) P := by
    change IsBrownianReal (fun t : ℝ≥0 => B (- -(t : ℝ))) P
    simpa only [neg_neg] using hB
  have hBCrev : IndepFun (fun ω t => positiveArm Br t ω) (fun ω t => negativeArm Br t ω) P := by
    simpa only [Br, positiveArm, negativeArm, neg_neg] using hBC.symm
  have hDrev : ∀ᵐ ω ∂P, ∀ n : ℤ, height Br d n ω ≤ height Br d (-D ω : ℤ) ω := by
    filter_upwards [hD] with ω hω n
    simpa only [Br, height_reflect, Int.cast_neg, neg_neg] using hω (-n)
  have hTrev : ∀ᵐ ω ∂P, ∀ t : ℝ, height Br d t ω ≤ height Br d (-T ω) ω := by
    filter_upwards [hT] with ω hω t
    simpa only [Br, height_reflect, neg_neg] using hω (-t)
  have hDL : ∀ y ≥ 1, L * tailScale d y ≤ P.real {ω | (D ω : ℝ) ≤ -y} := by
    intro y hy
    refine (lattice_argmax_right_lower hBrev hCrev hBCrev hd hy
      (D := fun ω => -D ω) hDrev).trans (measureReal_mono ?_)
    intro ω hω
    change y < ((-D ω : ℤ) : ℝ) at hω
    rw [Int.cast_neg] at hω
    change (D ω : ℝ) ≤ -y
    linarith
  have hTL : ∀ y ≥ 1, P.real {ω | T ω ≤ -y} ≤ V * tailScale d y := by
    intro y hy
    refine (measureReal_mono ?_).trans
      (continuous_argmax_right_upper hBrev hd hy (T := fun ω => -T ω) hTrev)
    intro ω hω
    change T ω ≤ -y at hω
    change y ≤ -T ω
    linarith
  have hUdecay : U * decay d r ≤ L :=
    (mul_le_mul_of_nonneg_right (by linarith : U ≤ U + V) (decay_pos _ _).le).trans hdecay
  have hVdecay : V * decay d r ≤ L :=
    (mul_le_mul_of_nonneg_right (by linarith : V ≤ U + V) (decay_pos _ _).le).trans hdecay
  have hCast : Measurable (fun n : ℤ => (n : ℝ)) := measurable_of_countable _
  have hDC : AEMeasurable (fun ω => (D ω : ℝ)) P := hCast.comp_aemeasurable hDM
  exact compare_from_tails hU.le hV.le hr hUdecay hVdecay hDC hTM hDR hTR hDL hTL x

end GaussianWalkSurvival

theorem OMA.solution : type_of% @OMA.S_mo_142880.main := by
  intro d hd
  obtain ⟨b, hb⟩ := GaussianWalkSurvival.brownianArgmaxShift d hd
  refine ⟨1, b, by norm_num, ?_⟩
  intro Ω mΩ P hP B hB hC hBC D T hDM hTM hD hT x
  simpa only [one_mul] using hb Ω P B hB hC hBC D T hDM hTM hD hT x
