import Mathlib

/-!
# A398140: Numbers m such that the distinct prime factors of the product m*(m+1)*(m+2)*(m+3) are all consecutive primes beginning with 2 (that is, the product is a term of A055932).

Source: https://oeis.org/A398140
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A398140 (Ken Clements, Jul 21 2026): There are no more
terms in this sequence past 63.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 5, 7, 63, ...).
* A positive integer N is prime-complete when its distinct prime factors are consecutive primes
  beginning with 2: whenever a prime p divides N, every smaller prime q divides N (helper `PC`).
* The terms are the positive integers m with m*(m+1)*(m+2)*(m+3) prime-complete; the conjecture is
  stated as: every such m is at most 63.
-/

namespace OMA.S_oeis_a398140

/-- The distinct prime factors of N are consecutive primes beginning with 2. -/
def PC (N : ℕ) : Prop := ∀ p q : ℕ, p.Prime → q.Prime → q < p → p ∣ N → q ∣ N

/-- The conjecture recorded in A398140. -/
theorem main : ∀ m : ℕ, 0 < m → PC (m * (m + 1) * (m + 2) * (m + 3)) → m ≤ 63 := by
  sorry

end OMA.S_oeis_a398140
