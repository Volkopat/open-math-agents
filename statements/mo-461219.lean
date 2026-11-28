import Mathlib

/-!
# A totient divisibility condition for primality

Source: https://mathoverflow.net/questions/461219
-/

open scoped BigOperators

namespace OMA.S_mo_461219

/-- If the totient of `2 * n ^ 2` divides the sum of the positive divisors of
`4 * n ^ 2 - 1`, then `2 * n - 1` is prime, for every natural number `n > 1`. -/
theorem main :
    ∀ n : ℕ, 1 < n →
      (Nat.totient (2 * n ^ 2) ∣ ∑ d ∈ (4 * n ^ 2 - 1).divisors, d) →
      (2 * n - 1).Prime := by
  sorry

end OMA.S_mo_461219
