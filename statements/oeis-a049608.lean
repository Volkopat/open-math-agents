import Mathlib

/-!
# A recurrence for OEIS A049608

Source: https://oeis.org/A049608
Credit: @hermitokatt

The sequence (offset 0) is `a(n) = T(n, n+2)` for the array `T` of A049600 (paths with
nonvertical segments). We use the formula listed in A049600 (Paul D. Hanna, Oct 06 2006),
`T(n, k) = Sum_{j=0..n-1} C(k+j, j) C(n-1, j)`, as the definition of `T`; it reproduces the
data of A049600 and of A049608 (0, 1, 6, 34, 190, 1059, 5908, …).

The conjecture (R. J. Mathar, Oct 26 2015):
`(n-1)(2n-1)(n+2) a(n) - 12 n (n-1)(n+1) a(n-1) + (n-2)(2n+1)(n+1) a(n-2) = 0`.

Reading.
* The recurrence is stated for every `n` for which all three terms are defined, i.e. `n ≥ 2`
  (checked numerically for `2 ≤ n ≤ 59`).
* For `n = 0` the sum is empty, so `T(0, k) = 0`, matching `a(0) = 0`.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a049608

/-- The array A049600, by Hanna's formula. -/
def T (n k : ℕ) : ℤ := ∑ j ∈ Finset.range n, ((k + j).choose j : ℤ) * ((n - 1).choose j : ℤ)

/-- A049608: `a(n) = T(n, n+2)`. -/
def a (n : ℕ) : ℤ := T n (n + 2)

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) - 1) * (2 * (n : ℤ) - 1) * ((n : ℤ) + 2) * a n
      - 12 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) + 1) * a (n - 1)
      + ((n : ℤ) - 2) * (2 * (n : ℤ) + 1) * ((n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a049608
