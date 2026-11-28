import Mathlib

/-!
# A073783: First differences of composite numbers.

Source: https://oeis.org/A073783
Credit: @EmircanEsen

Conjecture (R. J. Mathar, Jul 17 2026): a(n) = A065310(n+1).

Here
* A002808 lists the composite numbers `4, 6, 8, 9, 10, 12, …` (offset 1), and
  A073783(n) = A002808(n+1) - A002808(n) for `n ≥ 1`: `2, 2, 1, 1, 2, 2, 1, 1, …`;
* A065308(j) = prime(j - π(j)) for `j ≥ 1` (offset 1): `2, 2, 2, 3, 3, 5, 5, 7, …`;
* A065310(n) is the number of occurrences of the `n`-th prime in A065308 (offset 1):
  `3, 2, 2, 1, 1, 2, 2, 1, …`.

Formalization notes:
* `prime k` is the `k`-th prime with OEIS indexing, `prime 1 = 2`, i.e.
  `Nat.nth Nat.Prime (k - 1)`. For `j ≥ 1` the index `j - π(j)` counts the non-primes in
  `1, …, j`, so it is at least `1` (the number `1` is not prime) and `prime 0` is never used.
* A065310(n) is the number of indices `j ≥ 1` with A065308(j) = prime(n). This set is finite
  (`j - π(j)` tends to infinity), so `Set.ncard` gives its size.
-/

namespace OMA.S_oeis_a073783

/-- The `k`-th prime with OEIS indexing: `prime 1 = 2`, `prime 2 = 3`, …. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A002808, offset 1: `composite n` is the `n`-th composite number (`composite 1 = 4`). -/
noncomputable def composite (n : ℕ) : ℕ := Nat.nth (fun m => 1 < m ∧ ¬ m.Prime) (n - 1)

/-- A073783, offset 1: the first differences of the composite numbers. -/
noncomputable def a (n : ℕ) : ℕ := composite (n + 1) - composite n

/-- A065308, offset 1: `A065308 j = prime (j - π(j))`. -/
noncomputable def A065308 (j : ℕ) : ℕ := prime (j - Nat.primeCounting j)

/-- A065310, offset 1: the number of `j ≥ 1` with `A065308 j = prime n`. -/
noncomputable def A065310 (n : ℕ) : ℕ := {j : ℕ | 1 ≤ j ∧ A065308 j = prime n}.ncard

/-- Mathar's conjecture: the first differences of the composite numbers are A065310 shifted by
one. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = A065310 (n + 1) := by
  sorry

end OMA.S_oeis_a073783
