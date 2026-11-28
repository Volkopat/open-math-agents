import Mathlib

/-!
# A recurrence for OEIS A228329

Source: https://oeis.org/A228329
Credit: @hermitokatt

The sequence (offset 0): `a(n) = Sum_{k=0..n} (k+1)^2 T(n,k)^2`, where `T(n,k)` is the Catalan
triangle A039598, `T(n,k) = (k+1)/(n+1) * C(2n+2, n-k)` for `0 ≤ k ≤ n`
(rows 1; 2, 1; 5, 4, 1; …). Data: 1, 8, 98, 1320, 18590, ….

The conjecture (R. J. Mathar, Sep 08 2013):
`n(2n+1) a(n) + 2(-26n^2+25n-11) a(n-1) + 20(4n-5)(4n-7) a(n-2) = 0`.

Reading.
* The recurrence is stated for every `n` for which all three terms are defined, i.e. `n ≥ 2`
  (checked numerically for `2 ≤ n ≤ 44`).
* `T(n,k)` is computed in `ℚ` (it is an integer, but the formula has a division); the
  terms and coefficients are in `ℚ` so the negative coefficients are exact.
-/

namespace OMA.S_oeis_a228329

/-- The Catalan triangle A039598: `T(n,k) = (k+1)/(n+1) * C(2n+2, n-k)`. -/
def T (n k : ℕ) : ℚ := ((k : ℚ) + 1) / ((n : ℚ) + 1) * ((2 * n + 2).choose (n - k) : ℚ)

/-- A228329. -/
def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), ((k : ℚ) + 1) ^ 2 * T n k ^ 2

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * (2 * (n : ℚ) + 1) * a n +
      2 * (-26 * (n : ℚ) ^ 2 + 25 * (n : ℚ) - 11) * a (n - 1) +
      20 * (4 * (n : ℚ) - 5) * (4 * (n : ℚ) - 7) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a228329
