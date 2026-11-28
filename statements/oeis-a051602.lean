import Mathlib

/-!
# OEIS A051602: Maximal number of squares formed by n points in the plane

Source: https://oeis.org/A051602
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let `a(n)` be the maximal number of squares whose vertices lie in a set of `n` points
in the plane `ℝ²`.

Conjecture: The asymptotic density of the natural numbers `n` for which no maximal
`n`-point configuration is formed by all integer grid points `ℤ²` inside some closed
disk in `ℝ²` is 0.
-/

namespace OMA.S_oeis_a051602

open Classical

def IsSquare (Q : Finset (ℝ × ℝ)) : Prop :=
  ∃ c v : ℝ × ℝ, v ≠ (0, 0) ∧
    Q = {(c.1 + v.1, c.2 + v.2), (c.1 - v.2, c.2 + v.1),
         (c.1 - v.1, c.2 - v.2), (c.1 + v.2, c.2 - v.1)}

noncomputable def numSquares (S : Finset (ℝ × ℝ)) : ℕ :=
  (S.powerset.filter (fun Q => IsSquare Q)).card

def IsCircleGrid (S : Finset (ℝ × ℝ)) : Prop :=
  ∃ c : ℝ × ℝ, ∃ r : ℝ, ∀ p : ℝ × ℝ,
    p ∈ S ↔ ∃ x y : ℤ, p = ((x : ℝ), (y : ℝ)) ∧
      (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ r ^ 2

def HasCircleGridMax (n : ℕ) : Prop :=
  ∃ S : Finset (ℝ × ℝ), S.card = n ∧ IsCircleGrid S ∧
    ∀ T : Finset (ℝ × ℝ), T.card = n → numSquares T ≤ numSquares S

theorem main :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => ¬ HasCircleGridMax n)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a051602
