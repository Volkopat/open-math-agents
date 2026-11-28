import Mathlib

/-!
# A recurrence for OEIS A113409

Source: https://oeis.org/A113409
Credit: @hermitokatt

The sequence (offset 0): a transform of the central binomial coefficients A001405, given in the
entry by `a(n) = Sum_{k=0..floor(n/2)} C(n-k, k) C(k, floor(k/2))`, used as the definition.
Data: 1, 1, 2, 3, 6, 11, 21, 39, 74, ….

The conjecture (R. J. Mathar, Nov 07 2012):
`(n+2) a(n) - 2(n+1) a(n-1) + (n-4) a(n-2) + 2 a(n-3) + 4(2-n) a(n-4) = 0`.

Reading.
* The recurrence is stated for every `n` for which all five terms are defined, i.e. `n ≥ 4`
  (checked numerically for `4 ≤ n ≤ 39`).
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a113409

/-- A113409. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k : ℤ) * (k.choose (k / 2) : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 2) * a n - 2 * ((n : ℤ) + 1) * a (n - 1) + ((n : ℤ) - 4) * a (n - 2) + 2 * a (n - 3) +
      4 * (2 - (n : ℤ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a113409
