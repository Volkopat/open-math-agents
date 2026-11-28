import Mathlib

/-!
# A138220: Primes of the form `(30k)^(2^m) + 1`

Source: https://oeis.org/A138220, conjecture of Richard R. Forberg (2021).
The sequence lists the positive values of `k` for `m = 1`. The conjecture asks
for a positive `k` for each nonnegative exponent index `m`.
-/

namespace OMA.S_oeis_a138220

theorem main : ∀ m : ℕ, ∃ k : ℕ, 0 < k ∧ ((30 * k) ^ (2 ^ m) + 1).Prime := by
  sorry

end OMA.S_oeis_a138220
