import Mathlib

/-!
# A398139: Numbers m such that the distinct prime factors of the product m*(m+1)*(m+2) are consecutive primes beginning with 2 (that is, the product is a term of A055932).

Source: https://oeis.org/A398139
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A398139 (Ken Clements, Jul 21 2026): There are no more
terms in this sequence past 440.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 5, 8, 14, 20, 48, 54, 98, 350, ...).
* A positive integer N is prime-complete when its distinct prime factors are consecutive primes
  beginning with 2: whenever a prime p divides N, every smaller prime q divides N (helper `PC`).
* The terms are the positive integers m with m*(m+1)*(m+2) prime-complete; the conjecture is
  stated as: every such m is at most 440.
-/

namespace OMA.S_oeis_a398139

/-- The distinct prime factors of N are consecutive primes beginning with 2. -/
def PC (N : ℕ) : Prop := ∀ p q : ℕ, p.Prime → q.Prime → q < p → p ∣ N → q ∣ N

/-- The conjecture recorded in A398139. -/
theorem main : ∀ m : ℕ, 0 < m → PC (m * (m + 1) * (m + 2)) → m ≤ 440 := by
  sorry

end OMA.S_oeis_a398139
