import Mathlib

/-!
# A recurrence for OEIS A027182

Source: https://oeis.org/A027182
Credit: @hermitokatt

A027170 is the 4-diamondization of Pascal's triangle: with
`t(n, k) = C(n+2, k+1) + C(n+1, k) + C(n+1, k+1) + C(n, k)`, it sets
`T(n, k) = t(n, k) - t(0, 0) + 1 = t(n, k) - 4` for `0 ≤ k ≤ n`.
A027182 (offset 1) is the self-convolution of row `n`,
`a(n) = Sum_{k=0..n} T(n, k) T(n, n-k)`; data 18, 150, 820, 3726, 15492, ….

The conjecture (R. J. Mathar, May 06 2026):
`2(n+2) a(n) + (-17n-23) a(n-1) + (47n+36) a(n-2) + 2(-22n-17) a(n-3) + 4(-n+20) a(n-4)
 + 8(2n-9) a(n-5) + 24(12n-47) = 0`.

Reading.
* The offset is 1, so the recurrence is stated for every `n` for which all six terms lie in the
  sequence, i.e. `n ≥ 6` (checked numerically for `6 ≤ n ≤ 59`).
* `t(0, 0) = 5`, so `T(n, k) = t(n, k) - 4`; both factors have `0 ≤ k, n - k ≤ n`.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a027182

/-- Step 1 of the 4-diamondization of Pascal's triangle. -/
def t (n k : ℕ) : ℤ :=
  ((n + 2).choose (k + 1) : ℤ) + ((n + 1).choose k : ℤ) + ((n + 1).choose (k + 1) : ℤ) + (n.choose k : ℤ)

/-- The array A027170: `T(n, k) = t(n, k) - t(0, 0) + 1`. -/
def T (n k : ℕ) : ℤ := t n k - t 0 0 + 1

/-- A027182: the self-convolution of row `n` of A027170. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k * T n (n - k)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    2 * ((n : ℤ) + 2) * a n + (-17 * (n : ℤ) - 23) * a (n - 1) + (47 * (n : ℤ) + 36) * a (n - 2)
      + 2 * (-22 * (n : ℤ) - 17) * a (n - 3) + 4 * (-(n : ℤ) + 20) * a (n - 4)
      + 8 * (2 * (n : ℤ) - 9) * a (n - 5) + 24 * (12 * (n : ℤ) - 47) = 0 := by
  sorry

end OMA.S_oeis_a027182
