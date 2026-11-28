import Mathlib

/-!
# A234269: Mathar's recurrence

Source: https://oeis.org/A234269
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A234269 (offset 0): expansion of (1-2*x^2-sqrt(1-4*x^2-4*x^3))/(2*x*sqrt(1-4*x^2-4*x^3));
data 0, 0, 1, 1, 4, 7, 18, 39, 90, 206, 470, 1085, ...

Conjecture (R. J. Mathar, Jan 24 2020): D-finite with recurrence
-(n+1)*(2*n-5)*a(n) - 2*n*(n-4)*a(n-1) + 4*(n-1)*(2*n-3)*a(n-2) + 2*(8*n^2-32*n+29)*a(n-3)
+ 4*(n-2)*(2*n-7)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2-4*x^3 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(2*x*S) = 1 - 2*x^2 - S;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-15)*(4) + (0)*(1) + (60)*(1) + (58)*(0) + (8)*(0) = 0.
-/

namespace OMA.S_oeis_a234269

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A234269, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3 →
    coeff 0 S = 1 →
    G * (2 * X * S) = 1 - 2 * X ^ 2 - S →
    ∀ n : ℕ, 4 ≤ n →
      (5 + 3 * (n : ℚ) - 2 * (n : ℚ) ^ 2) * coeff n G + (8 * (n : ℚ) - 2 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (12 - 20 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 2) G + (58 - 64 * (n : ℚ) + 16 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (56 - 44 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a234269
