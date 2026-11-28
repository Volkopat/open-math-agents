import OMAStatements.S_mo_337998
import Mathlib

/-!
MathOverflow 337998: an instance of Iosif Pinelis's answer. Take the Bernoulli family: `ν` is
counting measure on the points `0` and `1` of `ℝ¹` and `c(x) = x`, so
`p(·, θ) = (1/(1 + e^θ), e^θ/(1 + e^θ))`. For `θ = ± log 3` the square roots are
`(1/2, √3/2)` and `(√3/2, 1/2)`; their midpoint has squared `L²` norm `(2 + √3)/4 < 1`, so it is
not the square root of a probability density.
-/

namespace OMA.P337998

open MeasureTheory Filter OMA.S_mo_337998

/-- Counting measure on the two points `0` and `1` of `ℝ¹`. -/
noncomputable def ν : Measure (Fin 1 → ℝ) := Measure.dirac 0 + Measure.dirac 1

/-- The statistic `c(x) = x` (the Bernoulli family). -/
def c : (Fin 1 → ℝ) → (Fin 1 → ℝ) := id

instance : IsFiniteMeasure ν := by unfold ν; infer_instance

lemma integral_ν (f : (Fin 1 → ℝ) → ℝ) : ∫ x, f x ∂ν = f 0 + f 1 := by
  rw [ν, integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]

lemma integrable_ν (f : (Fin 1 → ℝ) → ℝ) : Integrable f ν :=
  (integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)

lemma mem_Θ (θ : Fin 1 → ℝ) : θ ∈ Θ ν c := integrable_ν _

lemma dens0 (θ : Fin 1 → ℝ) : dens ν c θ 0 = 1 / (1 + Real.exp (θ 0)) := by
  have hpos : 0 < 1 + Real.exp (θ 0) := by positivity
  simp only [dens, integral_ν, c, id, Fin.sum_univ_one, Pi.zero_apply, Pi.one_apply, mul_zero,
    mul_one, Real.exp_zero]
  rw [Real.exp_sub, Real.exp_log hpos, Real.exp_zero]

lemma dens1 (θ : Fin 1 → ℝ) : dens ν c θ 1 = Real.exp (θ 0) / (1 + Real.exp (θ 0)) := by
  have hpos : 0 < 1 + Real.exp (θ 0) := by positivity
  simp only [dens, integral_ν, c, id, Fin.sum_univ_one, Pi.zero_apply, Pi.one_apply, mul_zero,
    mul_one, Real.exp_zero]
  rw [Real.exp_sub, Real.exp_log hpos]

lemma at_points {f g : (Fin 1 → ℝ) → ℝ} (h : f =ᵐ[ν] g) : f 0 = g 0 ∧ f 1 = g 1 := by
  have h' := ae_add_measure_iff.1 h
  rw [ae_dirac_eq, ae_dirac_eq] at h'
  exact ⟨h'.1, h'.2⟩

lemma memLp (θ : Fin 1 → ℝ) : MemLp (dens ν c θ) 2 ν := by
  refine MemLp.of_bound ?_ (max |dens ν c θ 0| |dens ν c θ 1|) ?_
  · apply Continuous.aestronglyMeasurable
    unfold dens c
    fun_prop
  · rw [ν, ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq]
    exact ⟨by simp [Real.norm_eq_abs], by simp [Real.norm_eq_abs]⟩

lemma disproof_aux : ¬ (∀ (d n : ℕ) (ν : Measure (Fin d → ℝ)), SigmaFinite ν →
      ∀ c : (Fin d → ℝ) → (Fin n → ℝ), ContDiff ℝ 1 c →
      (∀ θ ∈ Θ ν c, MemLp (dens ν c θ) 2 ν) →
      ∀ θ₁ ∈ Θ ν c, ∀ θ₂ ∈ Θ ν c, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        ∃ θ ∈ Θ ν c, (fun x => a * √(dens ν c θ₁ x) + (1 - a) * √(dens ν c θ₂ x))
          =ᵐ[ν] fun x => √(dens ν c θ x)) := by
  intro h
  obtain ⟨θ, -, hθ⟩ := h 1 1 ν inferInstance c contDiff_id (fun θ _ => memLp θ)
    (fun _ => Real.log 3) (mem_Θ _) (fun _ => -Real.log 3) (mem_Θ _) (1 / 2) (by norm_num)
    (by norm_num)
  obtain ⟨h0, h1⟩ := at_points hθ
  simp only [dens0, dens1, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)] at h0 h1
  rw [show (1 : ℝ) / (1 + 3) = 1 / 4 by norm_num, show (1 : ℝ) / (1 + 3⁻¹) = 3 / 4 by norm_num]
    at h0
  rw [show (3 : ℝ) / (1 + 3) = 3 / 4 by norm_num, show (3 : ℝ)⁻¹ / (1 + 3⁻¹) = 1 / 4 by norm_num]
    at h1
  set u := √(1 / 4 : ℝ) with hu
  set v := √(3 / 4 : ℝ) with hv
  have hu2 : u ^ 2 = 1 / 4 := by rw [hu, Real.sq_sqrt (by norm_num)]
  have hv2 : v ^ 2 = 3 / 4 := by rw [hv, Real.sq_sqrt (by norm_num)]
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hp0 : 0 < 1 + Real.exp (θ 0) := by positivity
  have s0 := Real.sq_sqrt (show 0 ≤ 1 / (1 + Real.exp (θ 0)) by positivity)
  have s1 := Real.sq_sqrt (show 0 ≤ Real.exp (θ 0) / (1 + Real.exp (θ 0)) by positivity)
  rw [← h0] at s0
  rw [← h1] at s1
  have hsum : 1 / (1 + Real.exp (θ 0)) + Real.exp (θ 0) / (1 + Real.exp (θ 0)) = 1 := by
    field_simp
  nlinarith [mul_nonneg hu0 hv0]

end OMA.P337998

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_337998.main) := OMA.P337998.disproof_aux
