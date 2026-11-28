import Mathlib

/-!
# A239701: least k > 0 such that q(n) + k is prime, q(n) the strict partition number

Source: https://oeis.org/A239701

A239701 (offset 0): `a(n)` is the least `k > 0` such that `q(n) + k` is prime, where `q(n)` is
the number of strict partitions of `n` (partitions into distinct parts, A000009):
1, 1, 1, 1, 1, 2, 1, 2, 1, 3, …

Conjecture (Zhi-Wei Sun, as recorded in the entry by Sean A. Irvine, Mar 24 2014): `a(n) ≤ n`
for `n > 0`.

Since `a(n)` is the least positive `k` with `q(n) + k` prime, `a(n) ≤ n` holds exactly when some
`k` with `0 < k ≤ n` makes `q(n) + k` prime, and the conjecture is stated in that form.

Conventions: `q(n)` is the number of partitions of `n` into distinct parts, the cardinality of
Mathlib's finset `Nat.Partition.distincts n` (1, 1, 1, 2, 2, 3, 4, 5, … for `n = 0, 1, 2, …`).
Everything is in `ℕ`.
-/

namespace OMA.S_oeis_a239701

/-- The strict partition function A000009: the number of partitions of `n` into distinct
parts. -/
def strictPartitionNumber (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ Nat.Prime (strictPartitionNumber n + k) := by
  sorry

end OMA.S_oeis_a239701
