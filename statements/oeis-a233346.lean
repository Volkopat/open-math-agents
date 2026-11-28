import Mathlib

/-!
# A233346: Primes of the form p(k)^2 + q(m)^2 with k > 0 and m > 0, where p(.) is the partition function (A000041), and q(.) is the strict partition function (A000009).

Source: https://oeis.org/A233346
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A233346 (Zhi-Wei Sun, Dec 07 2013): The sequence
contains infinitely many terms.

Conventions:
* The sequence has offset 1 (data 2, 5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 101, ...).
* p(.) is the partition function A000041: p(z) is the cardinality of the Mathlib type
  `Nat.Partition z` (helper `p`).
* q(.) is the strict partition function A000009: q(m) is the number of partitions of m into
  distinct parts, the cardinality of the Mathlib finset `Nat.Partition.distincts m` (helper `q`).
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a233346

/-- p(n), the number of partitions of n. -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- q(m), the number of partitions of m into distinct parts (A000009). -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The conjecture recorded in A233346. -/
theorem main : Set.Infinite {r : ℕ | r.Prime ∧
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ r = p k ^ 2 + q m ^ 2} := by
  sorry

end OMA.S_oeis_a233346
