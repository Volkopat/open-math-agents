import Mathlib

/-!
# Doubling of oscillations on balls

Source: https://mathoverflow.net/questions/131288 (Axiom, CC BY-SA 3.0).
Credit: @connoranderson

A sufficient condition is a uniform degree bound for the restrictions to
lines. The bound is independent of the ambient dimension and of the domain.
For quadratics the common center cancels the constant term and improves the
doubling factor to four, attained by the square function. In contrast, a
single convex, 1-Lipschitz, piecewise affine function on a bounded interval
has no finite oscillation doubling constant.
-/

namespace OMA.S_mo_131288
open Polynomial
noncomputable section

def osc {E : Type*} [PseudoMetricSpace E] (f : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  Metric.diam (f '' Metric.ball x r)

def lineDegree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (f : E → ℝ) (d : ℕ) : Prop :=
  ∀ x ∈ Ω, ∀ v : E, ∃ P : ℝ[X], P.natDegree ≤ d ∧
    ∀ t : ℝ, x + t • v ∈ Ω → P.eval t = f (x+t • v)

theorem main :
    (∀ (n d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ),
      lineDegree Ω f d → ∀ x r, 0 < r → Metric.ball x (2*r) ⊆ Ω → 0 < osc f x r →
        osc f x (2*r) ≤ |(Chebyshev.T ℝ d).eval 2| * osc f x r ∧
        (d ≤ 2 → osc f x (2*r) ≤ 4 * osc f x r)) ∧
    (osc (fun t : ℝ => t^2) 0 2 = 4 ∧ osc (fun t : ℝ => t^2) 0 1 = 1) ∧
    ¬ ∃ M : ℝ, ∀ x r : ℝ, 0 < r → Metric.ball x (2*r) ⊆ Set.Ioo (-4) 4 →
      0 < osc (fun t : ℝ => max t 0) x r →
        osc (fun t : ℝ => max t 0) x (2*r) ≤ M * osc (fun t : ℝ => max t 0) x r := by
  sorry

end
end OMA.S_mo_131288
