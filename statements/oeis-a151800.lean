import Mathlib

/-!
# A bound for the next prime in OEIS A151800

Thomas Ordowski's conjecture of 23 February 2023 concerns the least prime strictly
greater than n. It bounds this prime by n raised to the power n raised to 1/n,
for every natural n greater than three.

Source: https://oeis.org/A151800
Source text: OEIS Foundation, CC BY-SA 4.0.
Formalization credit: @rgoldman73-dev.
-/

namespace OMA.S_oeis_a151800

/-- The least prime strictly greater than n, as in OEIS A151800. -/
def a (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (n + 1))

/-- Both powers and the reciprocal are taken in the real numbers. -/
theorem main :
    ∀ n : ℕ, 3 < n →
      (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) := by
  sorry

end OMA.S_oeis_a151800
