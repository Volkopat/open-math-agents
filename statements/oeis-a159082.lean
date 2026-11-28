import Mathlib

/-!
# OEIS A159082: Numbers whose squares added to 7! are prime.

Source: https://oeis.org/A159082
Credit: @unserus

OEIS comments, stated together below:
"2) Sequence is conjectured to be infinite.
 3) It is conjectured that an infinite number of terms are primes.
 5) It is conjectured that an infinite number of a(n) are squares, first are 121=11^2, ..."
The terms are the positive integers `k` with `k^2 + 7!` prime (`7! = 5040`; first term `13`).
-/

namespace OMA.S_oeis_a159082

/-- The terms of A159082: positive `k` such that `k^2 + 7!` is prime. -/
def a159082Set : Set ℕ := {k : ℕ | 0 < k ∧ (k ^ 2 + Nat.factorial 7).Prime}

/-- Comments 2), 3) and 5): the sequence is infinite, infinitely many terms are prime, and
infinitely many terms are perfect squares. -/
theorem main :
    a159082Set.Infinite ∧
      {k : ℕ | k ∈ a159082Set ∧ k.Prime}.Infinite ∧
      {k : ℕ | k ∈ a159082Set ∧ IsSquare k}.Infinite := by
  sorry

end OMA.S_oeis_a159082
