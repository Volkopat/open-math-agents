import Mathlib

/-!
# A261515: Primes of the form p(q) + p(r) with q and r both prime, where p(.) is the partition function given by A000041.

Source: https://oeis.org/A261515
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A261515): "The conjecture in A261513 implies that the current
sequence has infinitely many terms." The open statement formalized here is that consequence: there
are infinitely many primes of the form `p(q) + p(r)` with `q` and `r` both prime.

Conventions:
* `p(m)` is the number of partitions of `m` (A000041), `Fintype.card (Nat.Partition m)`
  (1, 1, 2, 3, 5, 7, 11, 15, … for `m = 0, 1, 2, …`), as in `statements/oeis-a261513.lean`.
* `q` and `r` range over all primes; `q = r` is not excluded, as in the OEIS program (it never
  gives a prime, since `2 * p(q)` with `p(q) ≥ 2` is composite).

With these definitions the terms start 5, 17, 59, 71, 103, 157, as in the OEIS data (for example
`p(2) + p(3) = 2 + 3 = 5`), and the 421 terms of the b-file below `p(1511)` are reproduced.
-/

namespace OMA.S_oeis_a261515

/-- The partition function `p(m)` (A000041): the number of partitions of `m`. -/
def partitionCount (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The terms of A261515: primes of the form `p(q) + p(r)` with `q` and `r` both prime. -/
def S : Set ℕ :=
  {n : ℕ | n.Prime ∧ ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ n = partitionCount q + partitionCount r}

/-- A261515 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a261515
