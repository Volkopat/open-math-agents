import Mathlib

/-!
# Gradient norm at a fixed distance from the minimizer set

Source: kd202149, https://mathoverflow.net/questions/486704 (CC BY-SA 4.0).
Credit: @connoranderson. Pietro Majer gave geometric and gradient-flow arguments
in the original discussion. The strengthened conclusion follows by interpolating
between two linear tilts of the objective and minimizing on compact sets.

The minimum gradient norm over points at distance at least δ is attained at
distance exactly δ. For every exterior point, a boundary gradient is a scalar
multiple of its gradient, with scalar between zero and one.
-/

namespace OMA.S_mo_486704
open Set Metric
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
def minimizers {d : ℕ} (f : E d → ℝ) : Set (E d) := {x | ∀ y, f x ≤ f y}

theorem main : ∀ (d : ℕ), 0 < d → ∀ (f : E d → ℝ), ConvexOn ℝ univ f →
    Differentiable ℝ f → (minimizers f).Nonempty → Bornology.IsBounded (minimizers f) →
    ∀ δ : ℝ, 0 < δ →
    (∃ z : E d, infDist z (minimizers f) = δ ∧ ∀ y : E d, δ ≤ infDist y (minimizers f) →
      ‖gradient f z‖ ≤ ‖gradient f y‖) ∧
    (∀ y : E d, δ < infDist y (minimizers f) → ∃ z : E d, infDist z (minimizers f) = δ ∧
      ∃ t ∈ Icc (0:ℝ) 1, gradient f z = t • gradient f y) := by
  sorry
end OMA.S_mo_486704
