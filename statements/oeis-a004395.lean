import Mathlib

/-!
# A004395: Mathar's recurrence for the sequence with ratios 1, 1, 2, 3, 3, 4, 5, 5, 6, ...

Source: https://oeis.org/A004395
Credit: @ivillar

A004395 (offset 0): the sequence starting with 1 whose ratios of successive terms are
1, 1, 2, 3, 3, 4, 5, 5, 6, 7, 7, ...; data 1, 1, 1, 2, 6, 18, 72, 360, 1800, 10800, 75600, ...

Conjecture (R. J. Mathar, Sep 14 2025): the sequence is D-finite with recurrence
243*a(n) - 216*a(n-1) + 54*(-2*n+3)*a(n-2) + 6*(-12*n^3+60*n^2-87*n+28)*a(n-3)
+ 4*(2*n-5)*(2*n-7)*(n-3)*a(n-4) = 0.

Formalization: the ratio sequence repeats each odd number twice and then gives the next even
number, so the ratio a(n+1)/a(n) is floor((2*n+3)/3) (values 1, 1, 2, 3, 3, 4, 5, 5, 6, ...).
The terms are integers and the recurrence is stated for every n ≥ 4, the range in which a(n-4) is
defined.
-/

namespace OMA.S_oeis_a004395

/-- a(0) = 1 and a(n+1) = a(n) * floor((2n+3)/3). -/
def a : ℕ → ℤ
  | 0 => 1
  | (n + 1) => a n * (((2 * n + 3) / 3 : ℕ) : ℤ)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    243 * a n - 216 * a (n - 1) + 54 * (-2 * (n : ℤ) + 3) * a (n - 2) +
      6 * (-12 * (n : ℤ) ^ 3 + 60 * (n : ℤ) ^ 2 - 87 * n + 28) * a (n - 3) +
      4 * (2 * (n : ℤ) - 5) * (2 * (n : ℤ) - 7) * ((n : ℤ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a004395
