import Mathlib

/-!
# Two recurrences for OEIS A049609

Source: https://oeis.org/A049609
Credit: @hermitokatt

The sequence (offset 0) is `a(n) = T(n, n+3)` for the array `T` of A049600 (paths with
nonvertical segments). We use the formula listed in A049600 (Paul D. Hanna, Oct 06 2006),
`T(n, k) = Sum_{j=0..n-1} C(k+j, j) C(n-1, j)`, as the definition of `T`; it reproduces the
data of A049600 and of A049609 (0, 1, 7, 43, 253, 1462, 8378, …).

The conjectures (R. J. Mathar, Oct 26 2015), both recorded in the entry:
`-(n+3)(n-1) a(n) + (7n^2+8n-9) a(n-1) + (-7n^2+8n+9) a(n-2) + (n+1)(n-3) a(n-3) = 0` and
`n(n+3)(n-1) a(n) - (2n+1)(3n^2+3n-4) a(n-1) + (n-2)(n+2)(n+1) a(n-2) = 0`.

Reading.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 3` for the
  first and `n ≥ 2` for the second (both checked numerically up to `n = 59`).
* For `n = 0` the sum is empty, so `T(0, k) = 0`, matching `a(0) = 0`.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a049609

/-- The array A049600, by Hanna's formula. -/
def T (n k : ℕ) : ℤ := ∑ j ∈ Finset.range n, ((k + j).choose j : ℤ) * ((n - 1).choose j : ℤ)

/-- A049609: `a(n) = T(n, n+3)`. -/
def a (n : ℕ) : ℤ := T n (n + 3)

/-- Mathar's two conjectured recurrences. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n →
      -((n : ℤ) + 3) * ((n : ℤ) - 1) * a n + (7 * (n : ℤ) ^ 2 + 8 * (n : ℤ) - 9) * a (n - 1)
        + (-7 * (n : ℤ) ^ 2 + 8 * (n : ℤ) + 9) * a (n - 2) + ((n : ℤ) + 1) * ((n : ℤ) - 3) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℤ) * ((n : ℤ) + 3) * ((n : ℤ) - 1) * a n
        - (2 * (n : ℤ) + 1) * (3 * (n : ℤ) ^ 2 + 3 * (n : ℤ) - 4) * a (n - 1)
        + ((n : ℤ) - 2) * ((n : ℤ) + 2) * ((n : ℤ) + 1) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a049609
