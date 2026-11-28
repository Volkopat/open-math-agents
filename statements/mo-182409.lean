import Mathlib

/-!
# Vertical zero-free strips for a bilateral Laplace transform

Chee asks for conditions guaranteeing a vertical zero-free strip. Bounded
support alone allows a zero in every such strip. The positive criterion uses
the size of an atom at the origin relative to all remaining mass.

Source: Chee, https://mathoverflow.net/questions/182409 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_182409
open MeasureTheory
noncomputable def transform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x, Complex.exp (z * (x:ℂ)) ∂μ

theorem main :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, x ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ z : ℂ, Integrable (fun x : ℝ => Complex.exp (z * x)) μ) ∧
      Differentiable ℂ (transform μ) ∧ (∀ z : ℂ, ‖transform μ z‖ ≤ Real.exp |z.re|) ∧
      (∀ q : ℚ, ∃ z : ℂ, z.re=q ∧ transform μ z=0) ∧
      ∀ a b : ℝ, a<b → ∃ z : ℂ, a<z.re ∧ z.re<b ∧ transform μ z=0) ∧
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], (∀ᵐ x ∂μ, |x|≤1) →
      ∀ R : ℝ, 0≤R → Real.exp R * (1-μ.real {0}) < μ.real {0} →
        ∀ z : ℂ, |z.re|≤R → transform μ z ≠ 0) := by
  sorry

end OMA.S_mo_182409
