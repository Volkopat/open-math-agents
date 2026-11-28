import Mathlib

/-!
# A recurrence for OEIS A025184

Source: https://oeis.org/A025184
Credit: @hermitokatt

A025177 is the array of first differences in the `(n, n)` direction of the trinomial array
A027907 (generating function `(1 - y z) / (1 - z (1 + y + y^2))`); it satisfies
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)`, starting with the rows `[1]` and `[1, 0, 1]`.
A025184 (offset 0) is `a(n) = T(2n, n)`; data 1, 1, 7, 35, 189, 1038, 5797, ….

The conjecture (R. J. Mathar, Feb 25 2015):
`33n(3n-1)(3n-2) a(n) + 11(2047n^3 - 10725n^2 + 17192n - 8520) a(n-1)
 + 9(-4397n^3 - 10169n^2 + 110500n - 145368) a(n-2) - 54(2n-5)(5353n^2 - 33313n + 53904) a(n-3)
 - 115668(2n-5)(2n-7)(n-4) a(n-4) = 0`.

Reading.
* The recurrence is stated for every `n` for which all five terms lie in the sequence, i.e.
  `n ≥ 4` (checked numerically for `4 ≤ n ≤ 59`).
* `T` is defined by the recursion and the two initial rows given in A025177; the terms with
  `k - 1 < 0` or `k - 2 < 0` are omitted. Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a025184

/-- A025177: the first differences in the `(n, n)` direction of the trinomial array A027907,
read by rows: `T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)`, starting with the rows `[1]` and
`[1, 0, 1]`. Entries with `k < 0` are absent (they are `0`), and `T(n, k) = 0` for `k > 2n`. -/
def T : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 2 then 1 else 0
  | n + 2, k => T (n + 1) k + (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      (if 2 ≤ k then T (n + 1) (k - 2) else 0)

/-- A025184: `a(n) = T(2n, n)`. -/
def a (n : ℕ) : ℤ := T (2 * n) n

/-- Mathar's conjectured recurrence, for all `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    33 * (n : ℤ) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) - 2) * a n
      + 11 * (2047 * (n : ℤ) ^ 3 - 10725 * (n : ℤ) ^ 2 + 17192 * (n : ℤ) - 8520) * a (n - 1)
      + 9 * (-4397 * (n : ℤ) ^ 3 - 10169 * (n : ℤ) ^ 2 + 110500 * (n : ℤ) - 145368) * a (n - 2)
      - 54 * (2 * (n : ℤ) - 5) * (5353 * (n : ℤ) ^ 2 - 33313 * (n : ℤ) + 53904) * a (n - 3)
      - 115668 * (2 * (n : ℤ) - 5) * (2 * (n : ℤ) - 7) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025184
