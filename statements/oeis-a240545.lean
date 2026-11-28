import Mathlib

/-!
# A240545: Least k > 0 such that n + p(k) is prime, where p(k) is the number of partitions of k.

Source: https://oeis.org/A240545
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A240545 (Sean A. Irvine, Apr 07 2014): (Zhi-Wei Sun)
a(n) < n for n > 7.

Conventions:
* The sequence has offset 0 (data 2, 1, 1, 2, 1, 2, 1, 8, 3, 2, 1, 2, ...).
* p(n) is the number of partitions of n, the cardinality of the Mathlib type `Nat.Partition n`
  (helper `p`).
* a(n) is the least k > 0 such that n + p(k) is prime. The claim a(n) < n (which includes that
  a(n) exists) is stated as: there is such a k with 0 < k < n; this is the same as a(n) < n for
  the least such k.
-/

namespace OMA.S_oeis_a240545

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The conjecture recorded in A240545. -/
theorem main : ∀ n : ℕ, 7 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (n + p k).Prime := by
  sorry

end OMA.S_oeis_a240545
