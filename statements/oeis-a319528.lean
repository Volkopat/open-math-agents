import Mathlib

/-!
# A319528: a(n) = 8 * sigma(n).

Source: https://oeis.org/A319528
Credit: @bnb9001

Here sigma is the sum of divisors, `ArithmeticFunction.sigma 1`. The sequence has offset 1.

Conjecture: a(n) = sigma(7 n) = A283078(n) if and only if n is not a multiple of 7. The entry
notes that the conjecture is true, since sigma is multiplicative.
-/

namespace OMA.S_oeis_a319528

/-- For every `n ≥ 1`, `sigma (7 n) = 8 sigma n` if and only if `7` does not divide `n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (ArithmeticFunction.sigma 1 (7 * n) = 8 * ArithmeticFunction.sigma 1 n ↔ ¬ 7 ∣ n) := by
  sorry

end OMA.S_oeis_a319528
