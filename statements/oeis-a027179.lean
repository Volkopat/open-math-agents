import Mathlib

/-!
# A recurrence for OEIS A027179

Source: https://oeis.org/A027179
Credit: @hermitokatt

A027170 is the 4-diamondization of Pascal's triangle: with
`t(n, k) = C(n+2, k+1) + C(n+1, k) + C(n+1, k+1) + C(n, k)`, it sets
`T(n, k) = t(n, k) - t(0, 0) + 1 = t(n, k) - 4` for `0 ≤ k ≤ n`.
A027179 (offset 0) is the half row sum `a(n) = T(n, 0) + T(n, 1) + … + T(n, floor(n/2))`;
data 1, 3, 15, 26, 81, 130, 350, ….

The conjecture (R. J. Mathar, May 06 2026):
`-(n+2)(3n-20) a(n) - (n+1)(3n-11) a(n-1) + (33n^2-180n-100) a(n-2) + (15n^2-56n+1) a(n-3)
 + 2(-51n^2+313n-208) a(n-4) - 12(n-1)(n-4) a(n-5) + 8(9n-11)(n-5) a(n-6)
 + 4(-24n^2+196n-365) = 0`.

Reading.
* The recurrence is stated for every `n` for which all seven terms are defined, i.e. `n ≥ 6`
  (checked numerically for `6 ≤ n ≤ 59`).
* `t(0, 0) = 5`, so `T(n, k) = t(n, k) - 4`; the half row uses `k ≤ floor(n/2) ≤ n`.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a027179

/-- Step 1 of the 4-diamondization of Pascal's triangle. -/
def t (n k : ℕ) : ℤ :=
  ((n + 2).choose (k + 1) : ℤ) + ((n + 1).choose k : ℤ) + ((n + 1).choose (k + 1) : ℤ) + (n.choose k : ℤ)

/-- The array A027170: `T(n, k) = t(n, k) - t(0, 0) + 1`. -/
def T (n k : ℕ) : ℤ := t n k - t 0 0 + 1

/-- A027179: the half row sums of A027170. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), T n k

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 2) * (3 * (n : ℤ) - 20) * a n - ((n : ℤ) + 1) * (3 * (n : ℤ) - 11) * a (n - 1)
      + (33 * (n : ℤ) ^ 2 - 180 * (n : ℤ) - 100) * a (n - 2)
      + (15 * (n : ℤ) ^ 2 - 56 * (n : ℤ) + 1) * a (n - 3)
      + 2 * (-51 * (n : ℤ) ^ 2 + 313 * (n : ℤ) - 208) * a (n - 4)
      - 12 * ((n : ℤ) - 1) * ((n : ℤ) - 4) * a (n - 5)
      + 8 * (9 * (n : ℤ) - 11) * ((n : ℤ) - 5) * a (n - 6)
      + 4 * (-24 * (n : ℤ) ^ 2 + 196 * (n : ℤ) - 365) = 0 := by
  sorry

end OMA.S_oeis_a027179
