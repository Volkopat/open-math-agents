import Mathlib

/-!
# A397790. The prime square closest to a prime cube

A397790 conjectures that the prime square closest to the cube of the n-th prime
is unique, and that it is the square of A397789(n), the prime nearest to the
square root of that cube. The entry also records Jianing Song's argument for
the no-tie assertion.

Both sequences start at n = 1. Quantifying over all primes q ranges over
exactly those inputs q = prime(n). The strict distance comparison expresses
uniqueness of the nearest square. The second comparison says that its prime
root also minimizes the ordinary distance to the square root of q³.

Source: https://oeis.org/A397790
Companion sequence: https://oeis.org/A397789
Credit: @AlfredMelson
-/

namespace OMA.S_oeis_a397790

theorem main : ∀ q : ℕ, q.Prime → ∃ r : ℕ, r.Prime ∧
    (∀ s : ℕ, s.Prime → s ≠ r →
      Nat.dist (r ^ 2) (q ^ 3) < Nat.dist (s ^ 2) (q ^ 3)) ∧
    (∀ s : ℕ, s.Prime →
      |(r : ℝ) - Real.sqrt ((q : ℝ) ^ 3)| ≤ |(s : ℝ) - Real.sqrt ((q : ℝ) ^ 3)|) := by
  sorry

end OMA.S_oeis_a397790
