import Mathlib

/-!
# A discrete iteration related to Pierce expansions

Source: https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions
(J. O. Shallit; see P. Erdős and J. Shallit, *New bounds on the length of finite Pierce and
Engel series*, Sém. Théor. Nombres Bordeaux 3 (1991), 43–53)
Credit: @ishaanzee

Let `a > b > 0` be integers. Set `b₁ = b` and `bᵢ₊₁ = a mod bᵢ`. Eventually `bₙ₊₁ = 0`; put
`P(a, b) = n`. For example `P(35, 22) = 7`, since the iterates are
`22, 13, 9, 8, 3, 2, 1, 0`. Shallit asks to prove or disprove `P(a, b) = O((log a)²)`
(the best known upper bound is of order `a^(1/3)`). We state the conjectured bound.

Formalization: `pierceLength a x` counts the nonzero terms of the sequence `x, a mod x,
a mod (a mod x), …` before it reaches `0` (the sequence strictly decreases while nonzero, since
`a mod x < x`), so `P(a, b) = pierceLength a b`. The `O`-bound over all pairs `a > b > 0` is
stated with an explicit constant: there is `C` with `P(a, b) ≤ C (log a)²` for all such pairs.
(Since `a ≥ 2` forces `log a ≥ log 2 > 0`, this is equivalent to the bound holding for all
sufficiently large `a`.)
-/

namespace OMA.S_opg_a_discrete_iteration_related_to_pierce_expansions

/-- The number of nonzero terms of `x, a mod x, a mod (a mod x), …` before the first `0`. -/
def pierceLength (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | x + 1 => pierceLength a (a % (x + 1)) + 1
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos x)

/-- **Shallit's conjecture**: `P(a, b) = O((log a)²)` for integers `a > b > 0`. -/
theorem main : ∃ C : ℝ, ∀ a b : ℕ, 0 < b → b < a →
    (pierceLength a b : ℝ) ≤ C * Real.log a ^ 2 := by
  sorry

end OMA.S_opg_a_discrete_iteration_related_to_pierce_expansions
