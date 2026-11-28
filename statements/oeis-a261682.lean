import Mathlib

/-!
# A261682: Mathar's recurrence

Source: https://oeis.org/A261682
Credit: @ivillar

The sequence a(n) = 2^n + (1 + (n mod 2)/2) * C(n+1, floor((n + (n mod 2))/2)) - 1 (offset 0;
data 1, 4, 6, 16, 25, 61, ...). R. J. Mathar conjectured (Jan 04 2017) the recurrence
-(n+2)*(15*n^2-29*n-56)*a(n) + 9*(5*n^3-3*n^2-24*n-20)*a(n-1)
  + 2*(15*n^3-14*n^2-219*n+158)*a(n-2) + 36*(-5*n^3+8*n^2+31*n-38)*a(n-3)
  + 8*(n-2)*(15*n^2+n-70)*a(n-4) = 0.

Formalization notes:
* The terms are computed in ℚ (the factor 1 + (n mod 2)/2 is 3/2 for odd n; the values are
  integers).
* The recurrence involves a(n-4), so it is stated for n ≥ 4.
-/

namespace OMA.S_oeis_a261682

/-- A261682: `2^n + (1 + (n mod 2)/2) * C(n+1, floor((n + (n mod 2))/2)) - 1`. -/
def a (n : ℕ) : ℚ :=
  2 ^ n + (1 + ((n % 2 : ℕ) : ℚ) / 2) * ((n + 1).choose ((n + n % 2) / 2) : ℚ) - 1

/-- Mathar's conjectured recurrence for A261682, for every `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℚ) + 2) * (15 * n ^ 2 - 29 * n - 56) * a n +
      9 * (5 * (n : ℚ) ^ 3 - 3 * n ^ 2 - 24 * n - 20) * a (n - 1) +
      2 * (15 * (n : ℚ) ^ 3 - 14 * n ^ 2 - 219 * n + 158) * a (n - 2) +
      36 * (-5 * (n : ℚ) ^ 3 + 8 * n ^ 2 + 31 * n - 38) * a (n - 3) +
      8 * ((n : ℚ) - 2) * (15 * n ^ 2 + n - 70) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a261682
