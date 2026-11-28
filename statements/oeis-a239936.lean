import Mathlib

/-!
# A239936: Least k > 0 such that p(k)+q(n) is prime, where p(n) is the number of partitions of n and q(n) is the number of strict partitions of n.

Source: https://oeis.org/A239936
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A239936 (Sean A. Irvine, Mar 29 2014): (Zhi-Wei Sun)
a(n) < n for n > 1.

Conventions:
* The sequence has offset 0 (data 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, ...).
* p(n) is the number of partitions of n, the cardinality of the Mathlib type `Nat.Partition n`
  (helper `p`).
* q(n) is the number of strict partitions of n (partitions into distinct parts): the number of
  elements of `Nat.Partition n` whose multiset of parts has no repeated element (helper `q`).
* a(n) is the least k > 0 such that p(k) + q(n) is prime. The claim a(n) < n (which includes that
  a(n) exists) is stated as: there is such a k with 0 < k < n; this is the same as a(n) < n for
  the least such k.
-/

namespace OMA.S_oeis_a239936

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- q(n), the number of strict partitions of n (partitions into distinct parts). -/
noncomputable def q (n : ℕ) : ℕ := Set.ncard {π : Nat.Partition n | π.parts.Nodup}

/-- The conjecture recorded in A239936. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (p k + q n).Prime := by
  sorry

end OMA.S_oeis_a239936
