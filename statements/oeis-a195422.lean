import Mathlib

/-!
# Two recurrences for OEIS A195422

Source: https://oeis.org/A195422
Credit: @hermitokatt

The sequence (offset 1): permanents of certain n X 2 cyclic (1,-1) matrices, given in the entry by
`a(n) = Sum_{k=0..n} (-2)^k * 2n * binomial(2n-k, k) * (n-k)! / (2n-k)`, used as the definition.
Data: -3, 2, 2, -8, 16, -16, 80, 384, ….

The entry records two conjectures (R. J. Mathar, Jul 20 2016):
1. `(-n+2) a(n) + (n^2-4n+6) a(n-1) + 2(n^2-2n+3) a(n-2) + 8(n-1) a(n-3) = 0`;
2. `a(n) - n a(n-1) - 8 a(n-2) + 4(n-4) a(n-3) + 16 a(n-4) = 0`.
`main` states both.

Reading.
* The offset is 1. Each recurrence is stated for every `n` for which all its terms are defined:
  `n ≥ 4` for the first, `n ≥ 5` for the second (both checked numerically up to `n = 39`).
* For `n ≥ 1` and `k ≤ n`, `2n - k ≥ n ≥ 1`, so the division and the natural-number subtractions
  are exact. (`a 0` is never used.)
* The summand has a division, so terms and coefficients are in `ℚ`.
-/

namespace OMA.S_oeis_a195422

/-- A195422. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (-2 : ℚ) ^ k * (2 * (n : ℚ)) * ((2 * n - k).choose k : ℚ) * ((n - k).factorial : ℚ) /
      ((2 * n - k : ℕ) : ℚ)

/-- Both of Mathar's conjectured recurrences. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (-(n : ℚ) + 2) * a n + ((n : ℚ) ^ 2 - 4 * (n : ℚ) + 6) * a (n - 1) +
        2 * ((n : ℚ) ^ 2 - 2 * (n : ℚ) + 3) * a (n - 2) + 8 * ((n : ℚ) - 1) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 5 ≤ n →
      a n - (n : ℚ) * a (n - 1) - 8 * a (n - 2) + 4 * ((n : ℚ) - 4) * a (n - 3) + 16 * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a195422
