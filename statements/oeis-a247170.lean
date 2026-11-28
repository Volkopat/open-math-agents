import Mathlib

/-!
# A247170: Mathar's recurrence

Source: https://oeis.org/A247170
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A247170 (offset 1): expansion of -3/2 + (x^3+3*x)/(sqrt(x^4-4*x^3-2*x^2+1)*2*x);
data 0, 2, 3, 2, 10, 11, 21, 50, 66, 152, 275, 467, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
(the entry also lists, from the same comment, a longer recurrence with linear coefficients)
n*(2*n-7)*a(n) + (n-1)*(2*n-9)*a(n-1) + 2*(-2*n^2+9*n-6)*a(n-2) + 2*(-6*n^2+33*n-38)*a(n-3)
+ 3*(-2*n^2+15*n-26)*a(n-4) + (2*n-5)*(n-5)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = x^4-4*x^3-2*x^2+1 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(2*x*S) = x^3 + 3*x - 3*x*S, which is the stated expression multiplied by 2*x*S;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (15)*(10) + (4)*(2) + (-22)*(3) + (-46)*(2) + (-3)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a247170

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A247170, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    G * (2 * X * S) = X ^ 3 + 3 * X - 3 * X * S →
    ∀ n : ℕ, 5 ≤ n →
      (-7 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * coeff n G + (9 - 11 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-12 + 18 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-76 + 66 * (n : ℚ) - 12 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-78 + 45 * (n : ℚ) - 6 * (n : ℚ) ^ 2) * coeff (n - 4) G + (25 - 15 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a247170
