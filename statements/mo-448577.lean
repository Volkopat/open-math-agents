import Mathlib

/-!
# A uniform logarithmic Sobolev bound for trigonometric exponential densities

Source: https://mathoverflow.net/questions/448577
Credit: @artnoage

The probability law has density proportional to the exponential of the given
trigonometric polynomial on [0, 2π]. The entropy is written as E[u log u] minus
E[u] log E[u], with u = f². This is the displayed normalized-log expression,
including the zero-test case by the usual continuous extension at zero.
Smooth tests are defined on ℝ and integrated over the displayed interval.
The counterexample can be chosen smooth and 2π-periodic.
-/

namespace OMA.S_mo_448577

open MeasureTheory
open scoped Interval

/-- The unnormalized trigonometric weight. -/
noncomputable def weight {N : ℕ} (X : Fin N → ℝ × ℝ) (θ : ℝ) : ℝ :=
  Real.exp (∑ k : Fin N,
    ((X k).1 * Real.cos (((k : ℝ) + 1) * θ) +
    (X k).2 * Real.sin (((k : ℝ) + 1) * θ)))

/-- Expectation with respect to the normalized weight on the displayed interval. -/
noncomputable def mean {N : ℕ} (X : Fin N → ℝ × ℝ) (g : ℝ → ℝ) : ℝ :=
  (∫ θ in 0..(2 * Real.pi), weight X θ * g θ) /
    (∫ θ in 0..(2 * Real.pi), weight X θ)

/-- Entropy of the square of a test function. -/
noncomputable def entropy {N : ℕ} (X : Fin N → ℝ × ℝ) (f : ℝ → ℝ) : ℝ :=
  mean X (fun θ ↦ f θ ^ 2 * Real.log (f θ ^ 2)) -
    mean X (fun θ ↦ f θ ^ 2) * Real.log (mean X (fun θ ↦ f θ ^ 2))

theorem main :
    ∀ N : ℕ, 0 < N → ∃ C : ℝ, 0 < C ∧
      ∀ (X : Fin N → ℝ × ℝ) (f : ℝ → ℝ), ContDiff ℝ ⊤ f →
        entropy X f ≤ C * mean X (fun θ ↦ deriv f θ ^ 2) := by
  sorry

end OMA.S_mo_448577
