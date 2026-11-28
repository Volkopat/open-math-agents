import Mathlib

/-!
# A350878: Integers m that divide the sum of values d*p < m, where d is a divisor of m, p is a prime, and d*p does not divide m.

Source: https://oeis.org/A350878
Credit: @agchua

Comment of A350878 (unsigned; the entry is by Devansh Singh, Jan 20 2022):
  Conjecture: The sum of values d*p < m in the definition of the sequence is equal to m for m = 5 only. True for m <= 15000.
The sequence has offset 1. As in the entry's programs (Mathematica, PARI, Python), sumDP m adds
d*p over all pairs (d, p) with d a divisor of m, p a prime, d*p < m and d*p not dividing m (two
different such pairs never give the same value d*p, since d1*p1 = d2*p2 with d1 ≠ d2 is the lcm
of d1 and d2, a divisor of m). The claim is stated for m ≥ 1, the range of the sequence: at m = 0
the divisor set Nat.divisors 0 is empty, so the sum would be 0 = m.
-/

namespace OMA.S_oeis_a350878

/-- The sum of d*p over the divisors d of m and the primes p with d*p < m and d*p not dividing m. -/
def sumDP (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, ∑ p ∈ (Finset.range m).filter (fun p => p.Prime ∧ d * p < m ∧ ¬ d * p ∣ m),
    d * p

/-- The comment's conjecture: for m ≥ 1 the sum equals m only for m = 5. -/
theorem main : ∀ m : ℕ, 1 ≤ m → (sumDP m = m ↔ m = 5) := by
  sorry

end OMA.S_oeis_a350878
