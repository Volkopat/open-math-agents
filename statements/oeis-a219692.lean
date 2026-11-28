import Mathlib

/-!
# A recurrence for OEIS A219692

Source: https://oeis.org/A219692
Credit: @hermitokatt

The sequence (offset 0):
`a(n) = Sum_{j=0..floor(n/3)} (-1)^j C(n,j) C(2j,j) C(2n-2j,n-j) (C(2n-3j-1,n) + C(2n-3j,n))`.
Data: 2, 6, 54, 564, 6390, 76356, ….

The conjecture (R. J. Mathar, Jun 14 2016), "D-finite with recurrence":
`n^3 a(n) - 2(2n-1)(7n^2-7n+3) a(n-1) + 12(4n-5)(n-1)(4n-3) a(n-2) = 0`.

Reading.
* No range is given. With the listed value `a(0) = 2` the identity fails at `n = 2`
  (the left side is `180`), and it holds numerically for `3 ≤ n ≤ 44`. A D-finite recurrence is
  read, as usual, as holding for all large `n`; the statement takes every `n` for which it can
  hold on the listed data, `n ≥ 3`, so `a(0)` is never used.
* For `n ≥ 1` and `j ≤ n/3` the upper index `2n-3j-1` is nonnegative, so the natural-number
  binomials and subtractions below agree with the integer formula.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a219692

/-- A219692. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n / 3 + 1),
    (-1 : ℤ) ^ j * (n.choose j : ℤ) * ((2 * j).choose j : ℤ) *
      ((2 * n - 2 * j).choose (n - j) : ℤ) *
      (((2 * n - 3 * j - 1).choose n : ℤ) + ((2 * n - 3 * j).choose n : ℤ))

/-- Mathar's conjectured recurrence, for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) ^ 3 * a n - 2 * (2 * (n : ℤ) - 1) * (7 * (n : ℤ) ^ 2 - 7 * (n : ℤ) + 3) * a (n - 1) +
      12 * (4 * (n : ℤ) - 5) * ((n : ℤ) - 1) * (4 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a219692
