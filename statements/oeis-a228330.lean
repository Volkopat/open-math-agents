import Mathlib

/-!
# A recurrence for OEIS A228330

Source: https://oeis.org/A228330
Credit: @hermitokatt

The sequence (offset 0): `a(n) = Sum_{k=0..n} (k+1)^4 T(n,k)^2`, where `T(n,k)` is the Catalan
triangle A039598, `T(n,k) = (k+1)/(n+1) * C(2n+2, n-k)` for `0 ≤ k ≤ n`
(rows 1; 2, 1; 5, 4, 1; …). This is `h(4)` in the OEIS name. Data: 1, 20, 362, 6504, 114686, ….

The conjecture (R. J. Mathar, Sep 08 2013):
`n(2n+1)(3467n-4029) a(n) + 8(-36721n^3 + 109040n^2 - 137926n + 69822) a(n-1) + 4(4n-9)(45706n-7907)(4n-7) a(n-2) = 0`.

Reading.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 2`
  (checked numerically for `2 ≤ n ≤ 44`).
* `T(n,k)` is computed in `ℚ` (it is an integer, but the formula has a division); the
  terms and coefficients are in `ℚ` so the negative coefficients are exact.
-/

namespace OMA.S_oeis_a228330

/-- The Catalan triangle A039598: `T(n,k) = (k+1)/(n+1) * C(2n+2, n-k)`. -/
def T (n k : ℕ) : ℚ := ((k : ℚ) + 1) / ((n : ℚ) + 1) * ((2 * n + 2).choose (n - k) : ℚ)

/-- A228330. -/
def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), ((k : ℚ) + 1) ^ 4 * T n k ^ 2

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * (2 * (n : ℚ) + 1) * (3467 * (n : ℚ) - 4029) * a n +
      8 * (-36721 * (n : ℚ) ^ 3 + 109040 * (n : ℚ) ^ 2 - 137926 * (n : ℚ) + 69822) * a (n - 1) +
      4 * (4 * (n : ℚ) - 9) * (45706 * (n : ℚ) - 7907) * (4 * (n : ℚ) - 7) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a228330
