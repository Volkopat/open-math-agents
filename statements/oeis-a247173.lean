import Mathlib

/-!
# A247173: Mathar's recurrence

Source: https://oeis.org/A247173
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A247173 (offset 0): expansion of g.f.
(-1)/(2*x^2+2*x) + (-2*x^3-3*x^2+1)/(sqrt(x^4+4*x^3-2*x^2-4*x+1)*(2*x^2+2*x));
data 1, 1, 7, 25, 101, 397, 1583, 6337, 25513, 103161, 418727, 1705129, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
-(n+1)*(3*n-4)*a(n) + (9*n^2-3*n-4)*a(n-1) + 2*(9*n^2-21*n+8)*a(n-2) + 2*(-3*n^2+n+8)*a(n-3)
+ (-15*n^2+53*n-12)*a(n-4) - (3*n-1)*(n-4)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = x^4+4*x^3-2*x^2-4*x+1 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(2*x^2+2*x)*S = -S - 2*x^3 - 3*x^2 + 1, which is the stated expression multiplied by
S*(2*x^2+2*x);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (-66)*(397) + (206)*(101) + (256)*(25) + (-124)*(7) + (-122)*(1) + (-14)*(1) = 0.
-/

namespace OMA.S_oeis_a247173

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A247173, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    G * ((2 * X ^ 2 + 2 * X) * S) = -S - 2 * X ^ 3 - 3 * X ^ 2 + 1 →
    ∀ n : ℕ, 5 ≤ n →
      (4 + (n : ℚ) - 3 * (n : ℚ) ^ 2) * coeff n G + (-4 - 3 * (n : ℚ) + 9 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (16 - 42 * (n : ℚ) + 18 * (n : ℚ) ^ 2) * coeff (n - 2) G + (16 + 2 * (n : ℚ) - 6 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-12 + 53 * (n : ℚ) - 15 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-4 + 13 * (n : ℚ) - 3 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a247173
