import Mathlib

/-!
# A277223: a(n) = A052489(n)/n.

Source: https://oeis.org/A277223
Credit: @ceejcake

Here A052489(n) is the largest number that is `n` times the sum of its decimal digits (or `0`
if there is no positive such number). Equivalently (first comment of the entry), `a(n)` is the
largest multiplier `k` such that `m = k*n` is `n` times the sum of its decimal digits, i.e. the
largest `k` with `digitsum(k*n) = k`, or `0` if there is no such positive `k`.

Conjecture (OEIS A277223, Robert Israel, Oct 06 2016): if `a(n) < 12` then `a(n) = 0` or `9`.
(The same comment first states, as a fact, that `a(n)` is never `1, 2, 3, 4, 5` or `6`; only the
conjecture sentence is formalized here.)

The conjecture is FALSE as written: for the 52-digit number
`N = 8181818181818181818181818181818181818181818181818182` one has
`11 * N = 90000000000000000000000000000000000000000000000000002`, whose digit sum is `11`, and no
`k ≥ 12` satisfies `digitsum(k * N) = k`, so `a(N) = 11`.

Formalization notes:
* The sequence has offset `1`; the conjecture is stated for all `n ≥ 1`.
* `digitsum m = (Nat.digits 10 m).sum`. Note `k = 0` always satisfies `digitsum(0 * n) = 0`,
  so the largest `k` with `digitsum(k * n) = k` is exactly `a(n)` (it is `0` when no positive
  `k` works, matching the entry's convention).
* Only finitely many `k` can work, and the search is cut off at the explicit bound
  `bound n = 36 + 18 * L`, where `L = (Nat.digits 10 n).length` is the number of digits of `n`.
  This loses nothing: if `digitsum(k * n) = k`, then, writing `len` for the number of decimal
  digits, `k = digitsum(k * n) ≤ 9 * len(k * n) ≤ 9 * (len k + L)` (since
  `k * n < 10 ^ len k * 10 ^ L`), and `18 * len k ≤ k + 36` for every `k` (for `k ≥ 1` with
  `j = len k ≥ 1` one has `k ≥ 10 ^ (j - 1)` and `18 * j ≤ 10 ^ (j - 1) + 36`). Hence
  `2 * k ≤ 18 * len k + 18 * L ≤ k + 36 + 18 * L`, i.e. `k ≤ 36 + 18 * L = bound n`.
* `a n` is the supremum (maximum, as a `Finset.sup` in `ℕ`) of the `k ≤ bound n` with
  `digitsum(k * n) = k`; this set always contains `0`.
* The definition is computable. Initial values for `n = 1, ..., 13`:
  `a(n) = 9, 9, 9, 12, 9, 9, 12, 9, 9, 9, 18, 9, 15`, and `a(62) = a(63) = 0`.
-/

namespace OMA.S_oeis_a277223

/-- Sum of the decimal digits of `m`. -/
def digitsum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- A lossless search bound for `a n` (see the formalization notes):
`36 + 18 * (number of decimal digits of n)`. -/
def bound (n : ℕ) : ℕ := 36 + 18 * (Nat.digits 10 n).length

/-- `a n` is the largest `k` such that `digitsum (k * n) = k` (this is `0` when no positive `k`
works). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (bound n + 1)).filter fun k => digitsum (k * n) = k).sup id

/-- Robert Israel's conjecture in OEIS A277223: if `a(n) < 12` then `a(n) = 0` or `a(n) = 9`.
This is false (see the module docstring). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n < 12 → a n = 0 ∨ a n = 9 := by
  sorry

end OMA.S_oeis_a277223
