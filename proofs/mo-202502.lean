import OMAStatements.S_mo_202502
import Mathlib

open MeasureTheory ProbabilityTheory in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_202502.main) := fun h => by
  have I (a t : ℝ) : Integrable (fun x : ℝ => Real.exp (t * x)) (.dirac a) := integrable_dirac (by simp)
  have J (t : ℝ) := ((I 0 t).smul_measure (c := 2⁻¹) (by simp)).add_measure ((I 2 t).smul_measure (c := 2⁻¹) (by simp))
  have := h (.dirac 1) _ inferInstance ⟨by simp [ENNReal.inv_two_add_inv_two]⟩ (fun t _ => ⟨I 1 t, J t, by
    simp only [mgf, id]
    rw [integral_add_measure ((I 0 t).smul_measure (by simp)) ((I 2 t).smul_measure (by simp))]
    simp [mul_two, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp t - 1)]⟩) (1 / 2)
  norm_num [Set.indicator] at this
