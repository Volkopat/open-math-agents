import Mathlib

/-!
# A recurrence for OEIS A026392

Source: https://oeis.org/A026392
Credit: @hermitokatt

The sequence (offset 1): a(n) = T(n, [n/2]), where `T` is the array in A026386.
Data: 1, 2, 4, 8, 17, 34, 75, 150, 339, 678, ….

The conjecture (R. J. Mathar, Feb 10 2015):
`(n+1) a(n) + 2(n-1) a(n-1) + 2(-3n+1) a(n-2) + 4(-3n+7) a(n-3) + 5(n-3) a(n-4) + 10(n-5) a(n-5) = 0`.

Reading.
* `T` is the array of A026386 given by its defining recurrence (`T(n,0) = T(n,n) = 1`, and for
  `1 ≤ k ≤ n-1`: `T(n,k) = T(n-1,k-1) + T(n-1,k)` for even `n`,
  `T(n,k) = T(n-1,k-1) + T(n-1,k) + T(n-2,k-1)` for odd `n`); `[n/2]` is `n / 2` in `ℕ`.
  This reproduces the listed data.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 6`
  (the offset is 1); checked numerically for `6 ≤ n ≤ 299`.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026392

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

/-- A026392: `a(n) = T(n, [n/2])`. -/
def a (n : ℕ) : ℤ := T n (n / 2)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * ((n : ℤ) - 1) * a (n - 1) + 2 * (-3 * (n : ℤ) + 1) * a (n - 2) +
      4 * (-3 * (n : ℤ) + 7) * a (n - 3) + 5 * ((n : ℤ) - 3) * a (n - 4) +
      10 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026392
