import Mathlib

/-!
# A recurrence for OEIS A228333

Source: https://oeis.org/A228333
Credit: @hermitokatt

The sequence (offset 0): `a(n) = Sum_{k=0..n} (k+1)^7 T(n,k)^2`, where `T(n,k)` is the Catalan
triangle A039598, `T(n,k) = (k+1)/(n+1) * C(2n+2, n-k)` for `0 ≤ k ≤ n`
(rows 1; 2, 1; 5, 4, 1; …). This is `h(7)` in the OEIS name. Data: 1, 132, 4260, 120400, 3017700, ….

The conjecture (R. J. Mathar, Dec 04 2013):
`n^2(304n-411) a(n) + 4(-1814n^3+2554n^2-4776n+7567) a(n-1) + 32(2n-5)(2n-1)(299n-176) a(n-2) = 0`.

Reading.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 2`
  (checked numerically for `2 ≤ n ≤ 44`).
* `T(n,k)` is computed in `ℚ` (it is an integer, but the formula has a division); the
  terms and coefficients are in `ℚ` so the negative coefficients are exact.
-/

namespace OMA.S_oeis_a228333

/-- The Catalan triangle A039598: `T(n,k) = (k+1)/(n+1) * C(2n+2, n-k)`. -/
def T (n k : ℕ) : ℚ := ((k : ℚ) + 1) / ((n : ℚ) + 1) * ((2 * n + 2).choose (n - k) : ℚ)

/-- A228333. -/
def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), ((k : ℚ) + 1) ^ 7 * T n k ^ 2

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) ^ 2 * (304 * (n : ℚ) - 411) * a n +
      4 * (-1814 * (n : ℚ) ^ 3 + 2554 * (n : ℚ) ^ 2 - 4776 * (n : ℚ) + 7567) * a (n - 1) +
      32 * (2 * (n : ℚ) - 5) * (2 * (n : ℚ) - 1) * (299 * (n : ℚ) - 176) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a228333
