import Mathlib

/-!
# A recurrence for OEIS A026389

Source: https://oeis.org/A026389
Credit: @hermitokatt

The sequence (offset 2): a(n) = number of integer strings s(0), …, s(n) counted by the array `T`
of A026386 that have s(n) = 4; also a(n) = T(2n, n-2).
Data: 1, 8, 49, 272, 1440, 7428, 37730, ….

The conjecture (R. J. Mathar, May 29 2013):
`(n+2) a(n) + 4(-3n-2) a(n-1) + 2(24n-19) a(n-2) + 4(-18n+43) a(n-3) + 35(n-4) a(n-4) = 0`.

Reading.
* We use the second description in the name, `a(n) = T(2n, n-2)`, with `T` the array of
  A026386 given by its defining recurrence (`T(n,0) = T(n,n) = 1`, and for `1 ≤ k ≤ n-1`:
  `T(n,k) = T(n-1,k-1) + T(n-1,k)` for even `n`, `T(n,k) = T(n-1,k-1) + T(n-1,k) + T(n-2,k-1)`
  for odd `n`). This reproduces the listed data, and agrees with a direct count of the strings
  (`s(0) = 0`, `s(i)` odd for odd `i`, `|s(i) - s(i-1)| ≤ 1`, `s(2n) = 4`) for `2 ≤ n ≤ 51`.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 6`
  (the offset is 2); checked numerically for `6 ≤ n ≤ 199`.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026389

/-- The array `T` of A026386: `T(n,0) = T(n,n) = 1`; for `1 ≤ k ≤ n-1`,
`T(n,k) = T(n-1,k-1) + T(n-1,k)` if `n` is even and
`T(n,k) = T(n-1,k-1) + T(n-1,k) + T(n-2,k-1)` if `n` is odd.
Entries with `k > n` are set to `0`; they are never used by the entries with `k ≤ n`. -/
def T : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if k = 0 ∨ k = n + 2 then 1
    else if n + 2 < k then 0
    else if (n + 2) % 2 = 0 then T (n + 1) (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k + T n (k - 1)

/-- A026389: `a(n) = T(2n, n-2)`. -/
def a (n : ℕ) : ℤ := T (2 * n) (n - 2)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 2) * a n + 4 * (-3 * (n : ℤ) - 2) * a (n - 1) + 2 * (24 * (n : ℤ) - 19) * a (n - 2) +
      4 * (-18 * (n : ℤ) + 43) * a (n - 3) + 35 * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026389
