import Mathlib

/-!
# Is every non-square cube a prime plus a square?

Source: https://math.stackexchange.com/questions/4984647

Conjecture: for every positive integer `a` that is not a perfect square, there is an integer
`b` such that `a³ - b²` is a (positive) prime. It has been checked for `a` up to a million.
The question asks to prove or disprove it.

Formalization notes:
* `main` states the conjecture as written.
* Since `b² = (-b)²`, it suffices to take `b : ℕ`; `a³ - b² = p` is written without
  subtraction as `b ^ 2 + p = a ^ 3`, with `p` a natural prime (so positive).
* "Not a perfect square" is `¬ IsSquare a`.
-/

namespace OMA.S_mse_4984647

/-- Every positive non-square `a` has some `b` with `a³ - b²` prime. -/
theorem main : ∀ a : ℕ, 0 < a → ¬ IsSquare a → ∃ b p : ℕ, p.Prime ∧ b ^ 2 + p = a ^ 3 := by
  sorry

end OMA.S_mse_4984647
