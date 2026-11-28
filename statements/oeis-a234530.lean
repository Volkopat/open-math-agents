import Mathlib

/-!
# A234530: Primes p with q(p) + 1 also prime, where q(.) is the strict partition function (A000009).

Source: https://oeis.org/A234530
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A234530): "By the conjecture in A234514, this sequence
should have infinitely many terms." That is, there are infinitely many primes `p` such that
`q(p) + 1` is also prime.

Conventions: `q(m)` is the number of partitions of `m` into distinct parts (A000009), the
cardinality of Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for
`m = 0, 1, 2, …`). With this definition the terms start 2, 3, 11, 13, 29, 37, as in the OEIS
data (for example `q(11) + 1 = 13`).
-/

namespace OMA.S_oeis_a234530

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The terms of A234530: primes `p` with `q(p) + 1` also prime. -/
def S : Set ℕ := {p : ℕ | p.Prime ∧ (q p + 1).Prime}

/-- Sun's conjecture: A234530 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a234530
