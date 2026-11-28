import Mathlib

/-!
# A233393: Primes of the form 2^k - 1 + q(m) with k > 0 and m > 0, where q(.) is the strict partition function (A000009).

Source: https://oeis.org/A233393
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A233393): The sequence has infinitely many terms.

The sequence lists the primes `p` such that `p = 2^k - 1 + q(m)` for some integers `k > 0` and
`m > 0`, where `q(m)` is the number of partitions of `m` into distinct parts (A000009), the
cardinality of Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for
`m = 0, 1, 2, …`). Since `2^k ≥ 1`, the subtraction `2^k - 1` in `ℕ` is exact. The conjecture
says that the set of these primes is infinite.
-/

namespace OMA.S_oeis_a233393

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The terms of A233393: primes of the form `2^k - 1 + q(m)` with `k > 0` and `m > 0`. -/
def S : Set ℕ := {p : ℕ | p.Prime ∧ ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ p = 2 ^ k - 1 + q m}

/-- Sun's conjecture: A233393 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a233393
