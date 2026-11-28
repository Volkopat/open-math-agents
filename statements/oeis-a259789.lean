import Mathlib

/-!
# A259789: Least integer k > 1 such that pi(k)*pi(k*n) is a square, where pi(.) is the prime-counting function given by A000720.

Source: https://oeis.org/A259789
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A259789 (Zhi-Wei Sun, Jul 05 2015), first sentence:
a(n) exists for any n > 0.

Conventions:
* The sequence has offset 1 (data 2, 27, 8, 2, 2, 9, 3, 5, 96, 10, 9, 2, ...).
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* `a(n) exists` is the statement that for every n > 0 there is an integer k > 1 such that
  pi(k)*pi(k*n) is a square; a(n) is then the least such k.
* `a square` is `IsSquare` on natural numbers.
* Only the first sentence of the conjecture is formalized; the `In general` sentence about
  positive rational numbers is a different statement.
-/

namespace OMA.S_oeis_a259789

/-- The conjecture recorded in A259789: for every n > 0 there is k > 1 with pi(k)*pi(k*n) a
square. -/
theorem main : ∀ n : ℕ, 0 < n →
    ∃ k : ℕ, 1 < k ∧ IsSquare (Nat.primeCounting k * Nat.primeCounting (k * n)) := by
  sorry

end OMA.S_oeis_a259789
