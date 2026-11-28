import Mathlib

/-!
# Does the equation σ(σ(x²)) = 2xσ(x) have any odd solutions?

Source: https://math.stackexchange.com/questions/3779447
(cross-posted as https://mathoverflow.net/questions/370047)

Let `σ` be the sum of divisors of a positive integer. A search up to `10⁶` finds only the
even solutions `x = 9516` and `x = 380640` of `σ(σ(x²)) = 2xσ(x)`. The asker conjectures that
there is no odd solution and asks whether one exists.

Formalization notes:
* `main` states the question in its "yes" reading: some odd positive integer `x` satisfies
  the equation (odd natural numbers are positive). The asker's conjecture is its negation.
* `σ` is Mathlib's `ArithmeticFunction.sigma 1`.
-/

namespace OMA.S_mse_3779447

open ArithmeticFunction

/-- Does `σ(σ(x²)) = 2xσ(x)` have an odd solution `x`? -/
theorem main : ∃ x : ℕ, Odd x ∧ sigma 1 (sigma 1 (x ^ 2)) = 2 * x * sigma 1 x := by
  sorry

end OMA.S_mse_3779447
