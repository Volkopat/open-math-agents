import Mathlib

/-!
# A259678: Primes of the form p(k)^2 + p(m)^2, where k and m are positive integers, and p(.) is the partition function given by A000041.

Source: https://oeis.org/A259678
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "The conjecture in A259531 implies that the current
sequence has infinitely many terms." The statement below is that consequence: the sequence has
infinitely many terms (the conjecture of A259531 itself is `statements/oeis-a259531.lean`).

Conventions:
* `p(m)` is the number of partitions of `m` (A000041: 1, 1, 2, 3, 5, 7, 11, ...), here
  `Fintype.card (Nat.Partition m)`.
* A term is a prime `q` with `q = p(k)^2 + p(m)^2` for some positive integers `k` and `m`
  (not necessarily distinct, in either order: `a(1) = 2 = p(1)^2 + p(1)^2`).
-/

namespace OMA.S_oeis_a259678

/-- The partition function `p(m)`. -/
def partitionCount (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The terms of A259678: primes of the form `p(k)^2 + p(m)^2` with `k, m > 0`. -/
def S : Set ℕ :=
  {q | q.Prime ∧ ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ q = partitionCount k ^ 2 + partitionCount m ^ 2}

/-- A259678 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a259678
