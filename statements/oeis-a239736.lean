import Mathlib

/-!
# A239736: Least k > 0 such that p(n)+p(k)-1 is prime, where p(n) is the number of partitions of n.

Source: https://oeis.org/A239736
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A239736 (Sean A. Irvine, Mar 25 2014): (Zhi-Wei Sun)
a(n) < n for n > 1.

Conventions:
* The sequence has offset 2 (data 1, 1, 1, 1, 1, 3, 2, 2, 2, 10, 3, 1, ...).
* p(n) is the number of partitions of n, the cardinality of the Mathlib type `Nat.Partition n`
  (helper `p`).
* a(n) is the least k > 0 such that p(n) + p(k) - 1 is prime. The claim a(n) < n (which includes
  that a(n) exists) is stated as: there is such a k with 0 < k < n; this is the same as a(n) < n
  for the least such k.
* The subtraction of 1 is exact since p(n) >= 1.
-/

namespace OMA.S_oeis_a239736

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The conjecture recorded in A239736. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (p n + p k - 1).Prime := by
  sorry

end OMA.S_oeis_a239736
