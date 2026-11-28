import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Algebra.BigOperators.Intervals

/-!
# A203472: a(n) = Product_{3 <= i < j <= n+2} (i + j)

Source: https://oeis.org/A203472
Credit: @SeanDishman

The entry (offset 1) states: it is conjectured that each term is divisible by the corresponding
superfactorial, A000178(n), as in A203474.

Conventions:
* `a n` is the product of `i + j` over `3 ≤ i < j ≤ n + 2`, written as the iterated product
  `∏_{j = 3}^{n + 2} ∏_{i = 3}^{j - 1} (i + j)`, which is the formula given in the entry.
  For `n = 1` the product is empty, so `a 1 = 1`; the first terms are
  `1, 7, 504, 498960, 8562153600`, as in the entry.
* A203474 is defined in the OEIS as `A203472(n) / A000178(n - 1)`, so the superfactorial
  corresponding to the `n`-th term is `A000178(n - 1) = 0! * 1! * ... * (n - 1)!`, which is
  `Nat.superFactorial (n - 1)` in Mathlib. With `A000178(n)` itself the claim already fails at
  `n = 2`, since `2` does not divide `7`.
-/

namespace OMA.S_oeis_a203472

/-- `a n = ∏_{3 ≤ i < j ≤ n + 2} (i + j)` (OEIS A203472, offset 1). -/
def a (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 3 (n + 2), ∏ i ∈ Finset.Ico 3 j, (i + j)

/-- Conjecture (OEIS A203472): every term is divisible by the corresponding superfactorial,
`A000178(n - 1) = Nat.superFactorial (n - 1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.superFactorial (n - 1) ∣ a n := by
  sorry

end OMA.S_oeis_a203472
