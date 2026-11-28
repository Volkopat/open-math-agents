import Mathlib

/-!
# A recurrence for OEIS A025187

Source: https://oeis.org/A025187
Credit: @hermitokatt

A025177 is the array of first differences in the `(n, n)` direction of the trinomial array
A027907 (generating function `(1 - y z) / (1 - z (1 + y + y^2))`); it satisfies
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)`, starting with the rows `[1]` and `[1, 0, 1]`.
A025187 (offset 1) is `a(n) = T(2n, n-1)`; data 1, 3, 16, 84, 459, 2552, 14378, ….

The conjecture (R. J. Mathar, Feb 25 2015):
`12n(1573n - 2085)(3n-1)(3n+1) a(n) + (259519n^4 - 6550685n^3 + 19840883n^2 - 20466403n + 6720078) a(n-1)
 - 54(2n-3)(63141n^3 - 343882n^2 + 645379n - 388606) a(n-2) - 324(n-3)(4693n - 5417)(2n-3)(2n-5) a(n-3) = 0`.

Reading.
* The offset is 1, so the recurrence is stated for every `n` for which all four terms lie in the
  sequence, i.e. `n ≥ 4` (checked numerically for `4 ≤ n ≤ 59`).
* `T` is defined by the recursion and the two initial rows given in A025177; the terms with
  `k - 1 < 0` or `k - 2 < 0` are omitted. Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a025187

/-- A025177: the first differences in the `(n, n)` direction of the trinomial array A027907,
read by rows: `T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)`, starting with the rows `[1]` and
`[1, 0, 1]`. Entries with `k < 0` are absent (they are `0`), and `T(n, k) = 0` for `k > 2n`. -/
def T : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 2 then 1 else 0
  | n + 2, k => T (n + 1) k + (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      (if 2 ≤ k then T (n + 1) (k - 2) else 0)

/-- A025187: `a(n) = T(2n, n-1)` for `n ≥ 1`. -/
def a (n : ℕ) : ℤ := T (2 * n) (n - 1)

/-- Mathar's conjectured recurrence, for all `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    12 * (n : ℤ) * (1573 * (n : ℤ) - 2085) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) + 1) * a n
      + (259519 * (n : ℤ) ^ 4 - 6550685 * (n : ℤ) ^ 3 + 19840883 * (n : ℤ) ^ 2 - 20466403 * (n : ℤ)
          + 6720078) * a (n - 1)
      - 54 * (2 * (n : ℤ) - 3) * (63141 * (n : ℤ) ^ 3 - 343882 * (n : ℤ) ^ 2 + 645379 * (n : ℤ) - 388606)
          * a (n - 2)
      - 324 * ((n : ℤ) - 3) * (4693 * (n : ℤ) - 5417) * (2 * (n : ℤ) - 3) * (2 * (n : ℤ) - 5) * a (n - 3)
      = 0 := by
  sorry

end OMA.S_oeis_a025187
