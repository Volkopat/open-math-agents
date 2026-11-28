import OMAStatements.S_mo_195973
import Mathlib

open MeasureTheory

namespace OMA.S_mo_195973

lemma half2 : (2⁻¹ : ENNReal) * 2 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma half2' : (2⁻¹ : ENNReal) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two

noncomputable def ν : Measure ℝ := (2⁻¹ : ENNReal) • (Measure.dirac 0 + Measure.dirac 1)

instance : IsProbabilityMeasure ν := by
  constructor
  simp [ν, Measure.dirac_apply', mul_add, half2']

lemma int_ν (f : ℝ → ℝ) : ∫ x, f x ∂ν = (f 0 + f 1) / 2 := by
  have hi : Integrable f (Measure.dirac 0 + Measure.dirac 1) :=
    integrable_add_measure.2 ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩
  rw [ν, integral_smul_measure, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp
  ring

lemma Iic_ν : ν (Set.Iic 0) = 2⁻¹ := by
  simp [ν, Measure.dirac_apply']

lemma Ici_ν : ν (Set.Ici 0) = 1 := by
  simp [ν, Measure.dirac_apply', mul_add, half2']

lemma integ_ν : Integrable id ν := by
  unfold ν
  exact (integrable_add_measure.2 ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩).smul_measure (by simp)

end OMA.S_mo_195973

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_195973.main) := by
  rintro ⟨c, hc, h⟩
  have h1 := h OMA.S_mo_195973.ν inferInstance OMA.S_mo_195973.integ_ν 0
    (by rw [OMA.S_mo_195973.Iic_ν])
    (by rw [OMA.S_mo_195973.Ici_ν]; norm_num)
  rw [OMA.S_mo_195973.int_ν] at h1
  simp only [sub_zero, abs_zero, abs_one] at h1
  have e : ∀ x : ℝ, ∫ y, |x - y| ∂OMA.S_mo_195973.ν = (|x - 0| + |x - 1|) / 2 := fun x =>
    OMA.S_mo_195973.int_ν (fun y => |x - y|)
  simp only [e] at h1
  rw [OMA.S_mo_195973.int_ν (fun x => (|x - 0| + |x - 1|) / 2)] at h1
  norm_num at h1
  linarith
