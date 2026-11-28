import Mathlib

/-!
# A233360: Primes of the form L(k) + q(m) with k > 0 and m > 0, where L(k) is the k-th Lucas number (A000204), and q(.) is the strict partition function (A000009).

Source: https://oeis.org/A233360
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A233360): "The sequence has infinitely many terms." That is,
there are infinitely many primes of the form `L(k) + q(m)` with `k > 0` and `m > 0`.

Conventions:
* `L(k)` is the `k`-th Lucas number, `L(0) = 2`, `L(1) = 1`, `L(k + 2) = L(k + 1) + L(k)`; for
  `k > 0` these are the terms 1, 3, 4, 7, 11, 18, … of A000204.
* `q(m)` is the number of partitions of `m` into distinct parts (A000009), the cardinality of
  Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for `m = 0, 1, 2, …`).

With these definitions the terms start 2, 3, 5, 7, 11, 13, as in the OEIS data (for example
`L(1) + q(1) = 1 + 1 = 2`), and all 270 terms of the b-file (up to 111521) are reproduced.
-/

namespace OMA.S_oeis_a233360

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (k + 2) = L (k + 1) + L k`. -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (k + 2) => L (k + 1) + L k

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The terms of A233360: primes of the form `L(k) + q(m)` with `k > 0` and `m > 0`. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ p = L k + q m}

/-- Sun's conjecture: A233360 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a233360
