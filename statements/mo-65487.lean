import Mathlib

/-!
# Equation σ(2z - 1) = 3z

Source: https://mathoverflow.net/questions/65487
Credit: @antonumias24-tech

The question: with `σ(h)` the sum of all positive divisors of `h`, are all solutions `z` of
`σ(2z - 1) = 3z` even numbers? The known solutions are `8, 104, 512, 1488, 9680, 73728, 603680`
(checked again by direct computation below `700000`) and `2508800`, all even.

Translation choices.
* `σ` is `ArithmeticFunction.sigma 1`, the sum of the positive divisors.
* `z` ranges over the positive integers, so `2 * z - 1` is a positive odd natural number and the
  natural-number subtraction does not truncate. (For `z = 0` the truncated equation would hold
  trivially; `0` is even anyway, but it is excluded to match the source.)
* The question asks whether every solution is even, and the expected answer is yes (no odd
  solution exists up to the range searched in the source), so `main` states that every positive
  solution is even.
-/

namespace OMA.S_mo_65487

theorem main : ∀ z : ℕ, 0 < z → ArithmeticFunction.sigma 1 (2 * z - 1) = 3 * z → Even z := by
  sorry

end OMA.S_mo_65487
