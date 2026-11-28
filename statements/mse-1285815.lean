import Mathlib

/-!
# Derivative Bound Inequality for Smooth Radial Functions on the Unit Ball

Source: https://math.stackexchange.com/questions/1285815/prove-or-disprove-an-inequality-on-bounds-of-derivatives-for-radial-functions
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Suppose `f : ℝ^n → ℝ` is a smooth radial function on the closed unit ball `B̄`,
i.e., `f(x) = g(‖x‖)` for `x ∈ B̄` with `f ∈ C^∞(B̄)`.
Prove or disprove that for every positive integer `k`,
`sup_{|α| = k, x ∈ B} |D^α f(x)| ≤ sup_{0 ≤ r < 1} |g^(k)(r)|`,
where `α` ranges over multi-indices of order `k` and `D^α f` is the corresponding
mixed derivative of `f`.

## Formalization Notes
For `f : EuclideanSpace ℝ (Fin n) → ℝ` smooth on `Metric.closedBall 0 1`, any
order-`k` coordinate derivative `D^α f(x)` corresponds to evaluating the `k`-th
iterated Fréchet derivative `iteratedFDeriv ℝ k f x` on a tuple of standard basis
vectors `v : Fin k → Fin n`. The radial profile `g : ℝ → ℝ` satisfies
`f x = g ‖x‖` on `closedBall 0 1`, and `iteratedDeriv k g r` is `g^(k)(r)`.
We state the inequality pointwise on `Metric.ball 0 1`: every upper bound `M` of
`|iteratedDeriv k g r|` over `r ∈ Set.Ioo 0 1` bounds every order-`k` coordinate derivative
(this avoids `sSup` junk values and the two-sided derivative at `r = 0`; by continuity of
`g^(k)` on `[0, 1]` the supremum over `(0, 1)` equals the one over `[0, 1)`).
-/

namespace OMA.S_mse_1285815

theorem main :
    ∀ (n k : ℕ), 0 < n → 0 < k →
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : ℝ → ℝ),
        ContDiffOn ℝ ⊤ f (Metric.closedBall 0 1) →
        (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = g ‖x‖) →
        ∀ M : ℝ, (∀ r ∈ Set.Ioo (0 : ℝ) 1, |iteratedDeriv k g r| ≤ M) →
        ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ idx : Fin k → Fin n,
          |iteratedFDeriv ℝ k f x (fun i => EuclideanSpace.single (idx i) (1 : ℝ))| ≤ M := by
  sorry

end OMA.S_mse_1285815
