import Mathlib

/-! Source: https://mathoverflow.net/questions/473425 -/

open MeasureTheory

noncomputable section

namespace OMA.S_mo_473425

def xMarginal (p : ℝ → ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, ∫ z, p x y z

def xzMarginal (p : ℝ → ℝ → ℝ → ℝ) (x z : ℝ) : ℝ :=
  ∫ y, p x y z

def yGivenX (p : ℝ → ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (∫ z, p x y z) / xMarginal p x

def yGivenXZ (p : ℝ → ℝ → ℝ → ℝ) (x z y : ℝ) : ℝ :=
  p x y z / xzMarginal p x z

/-- A joint density on the unit cube with differentiable conditional densities given
both variables and a Lipschitz conditional density with a cusp given only the first. -/
theorem main :
    ∃ p : ℝ → ℝ → ℝ → ℝ,
      let joint : ℝ × ℝ × ℝ → ℝ := fun w => p w.1 w.2.1 w.2.2
      Measurable joint ∧ Integrable joint ∧
      (∀ x y z, 0 ≤ p x y z) ∧
      (∀ x y z, p x y z ≠ 0 →
        x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ z ∈ Set.Icc 0 1) ∧
      (∫ w, joint w) = 1 ∧
      (∀ x, 0 < xMarginal p x →
        (∃ L : NNReal, LipschitzWith L (yGivenX p x)) ∧
        ¬ DifferentiableAt ℝ (yGivenX p x) (1 / 2)) ∧
      (∀ x z, 0 < xzMarginal p x z →
        Differentiable ℝ (yGivenXZ p x z) ∧
        ∃ L : NNReal, LipschitzWith L (deriv (yGivenXZ p x z))) := by
  sorry

end OMA.S_mo_473425
