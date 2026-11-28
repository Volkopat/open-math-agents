import Mathlib

/-!
# A233359: a(n) = |{0 < k < n: L(k) + q(n-k) is prime}|, where L(k) is the k-th Lucas number (A000204), and q(.) is the strict partition function (A000009).

Source: https://oeis.org/A233359
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A233359): "a(n) > 0 for all n > 1." That is, for every
`n > 1` there is some `k` with `0 < k < n` such that `L(k) + q(n - k)` is prime.

Conventions:
* `L(k)` is the `k`-th Lucas number, `L(0) = 2`, `L(1) = 1`, `L(k + 2) = L(k + 1) + L(k)`; for
  `k > 0` these are the terms 1, 3, 4, 7, 11, 18, … of A000204.
* `q(m)` is the number of partitions of `m` into distinct parts (A000009), the cardinality of
  Mathlib's finset `Nat.Partition.distincts m` (1, 1, 1, 2, 2, 3, 4, 5, … for `m = 0, 1, 2, …`).

With these definitions `a(1), …, a(10)` are 0, 1, 1, 2, 3, 1, 2, 4, 2, 2, as in the OEIS data
(for example `a(7) = 2` from `L(1) + q(6) = 5` and `L(6) + q(1) = 19`), and the first 1500 terms
of the b-file are reproduced.
-/

namespace OMA.S_oeis_a233359

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (k + 2) = L (k + 1) + L k`. -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (k + 2) => L (k + 1) + L k

/-- The strict partition function A000009: the number of partitions of `m` into distinct
parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- A233359: `a n` is the number of `k` with `0 < k < n` such that `L k + q (n - k)` is
prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k => (L k + q (n - k)).Prime)).card

/-- Sun's conjecture: `a(n) > 0` for all `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a233359
