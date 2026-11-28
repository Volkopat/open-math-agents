import Mathlib

/-!
# A239675: least k > 0 such that p(n) + k is prime, p(n) the partition number

Source: https://oeis.org/A239675

A239675 (offset 0): `a(n)` is the least `k > 0` such that `p(n) + k` is prime, where `p(n)` is
the number of partitions of `n`: 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, …  For example `a(3) = 2` because
`p(3) = 3` and `p(3) + 1 = 4` is composite, but `p(3) + 2 = 5` is prime.

Conjecture (Zhi-Wei Sun, as recorded in the entry by Sean A. Irvine, Mar 23 2014): `a(n) ≤ n`
for `n > 0`.

Since `a(n)` is the least positive `k` with `p(n) + k` prime, `a(n) ≤ n` holds exactly when some
`k` with `0 < k ≤ n` makes `p(n) + k` prime, and the conjecture is stated in that form.

Conventions: `p(n)` is the number of partitions of `n`, the cardinality of Mathlib's type
`Nat.Partition n` (1, 1, 2, 3, 5, 7, 11, 15, … for `n = 0, 1, 2, …`). Everything is in `ℕ`.
-/

namespace OMA.S_oeis_a239675

/-- The partition function A000041: the number of partitions of `n`. -/
def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ Nat.Prime (partitionNumber n + k) := by
  sorry

end OMA.S_oeis_a239675
