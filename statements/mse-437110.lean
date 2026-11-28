import Mathlib

/-!
# Odd perfect squares whose decimal digits are all 0 or 1

Source: https://math.stackexchange.com/questions/437110

Are there any odd perfect squares, apart from the trivial `1`, whose decimal representation
uses only the digits `1` and `0`?

Formalization notes:
* `main` states the question in its "yes" reading: some odd `x > 1` has `x²` with every
  decimal digit (`Nat.digits 10`) equal to `0` or `1`. An odd square other than `1` is exactly
  `x²` for an odd `x > 1`.
-/

namespace OMA.S_mse_437110

/-- Is there an odd square other than `1` whose decimal digits are all `0` or `1`? -/
theorem main : ∃ x : ℕ, Odd x ∧ 1 < x ∧ ∀ d ∈ Nat.digits 10 (x ^ 2), d = 0 ∨ d = 1 := by
  sorry

end OMA.S_mse_437110
