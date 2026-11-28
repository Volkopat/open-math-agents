import Mathlib

/-!
# A recurrence for OEIS A155858

Source: https://oeis.org/A155858
Credit: @hermitokatt

The sequence (offset 0): diagonal sums of triangle A155856, given in the entry by
`a(n) = Sum_{k=0..floor(n/2)} binomial(2n-3k, k) (n-2k)!`, used as the definition.
Data: 1, 1, 3, 9, 35, 168, 967, 6538, ….

The conjecture (R. J. Mathar, Feb 05 2015):
`a(n) - (n-1) a(n-1) - (n-2) a(n-2) + (n-3) a(n-3) + (n-10) a(n-4) - 5 a(n-5) + 3 a(n-6) + 3 a(n-7) = 0`.

Reading.
* The recurrence is stated for every `n` for which all eight terms are defined, i.e. `n ≥ 7`
  (checked numerically for `7 ≤ n ≤ 39`).
* For `k ≤ n/2` both `2n-3k` and `n-2k` are nonnegative, so the natural-number subtractions are exact.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a155858

/-- A155858. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((2 * n - 3 * k).choose k : ℤ) * ((n - 2 * k).factorial : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    a n - ((n : ℤ) - 1) * a (n - 1) - ((n : ℤ) - 2) * a (n - 2) + ((n : ℤ) - 3) * a (n - 3) +
      ((n : ℤ) - 10) * a (n - 4) - 5 * a (n - 5) + 3 * a (n - 6) + 3 * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a155858
