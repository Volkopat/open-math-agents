import FormalConjectures.Wikipedia.RamanujanTau
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! Compare the two discriminants and apply the complex triangle inequality. -/

namespace OMA.R_RamanujanTau_ramanujan_petersson_R1

open RamanujanTau UpperHalfPlane

/-- The formal Euler product gives the coefficients of the analytic discriminant. -/
def H1 : Prop :=
  ∀ n : ℕ, (τ n : ℂ) = (qExpansion 1 ModularForm.discriminant).coeff n

/-- The two Frobenius roots of the local polynomial have weight eleven. -/
def H2 : Prop :=
  ∀ p : ℕ, Prime p → ∃ α β : ℂ,
    (qExpansion 1 ModularForm.discriminant).coeff p = α + β ∧
    α * β = (p : ℂ) ^ 11 ∧
    ‖α‖ = (p : ℝ) ^ ((11 : ℝ) / 2) ∧ ‖β‖ = (p : ℝ) ^ ((11 : ℝ) / 2)

theorem main : H1 → H2 → type_of% @RamanujanTau.ramanujan_petersson := by
  intro hCoefficients hRoots p hp
  obtain ⟨α, β, hTrace, -, hα, hβ⟩ := hRoots p hp
  have hBound : ‖(τ p : ℂ)‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := calc
    ‖(τ p : ℂ)‖ = ‖α + β‖ := by rw [hCoefficients p, hTrace]
    _ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
    _ = _ := by rw [hα, hβ, two_mul]
  simpa only [Complex.norm_intCast, Int.cast_abs] using hBound

end OMA.R_RamanujanTau_ramanujan_petersson_R1
