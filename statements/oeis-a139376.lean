import Mathlib

/-!
# A139376: Mathar's recurrence

Source: https://oeis.org/A139376
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A139376 (offset 0): expansion of 1/((1-x^2*c(x))(1-x-x^2)) where c(x) is the g.f. of A000108;
data 1, 1, 3, 5, 11, 23, 54, 136, 374, 1103, 3441, 11186, ...

Conjecture (R. J. Mathar, Feb 05 2015):
(-n+1)*a(n) +6*(n-2)*a(n-1) +4*(-2*n+5)*a(n-2) +2*(-n+1)*a(n-3) +3*(3*n-7)*a(n-4) +3*(-n+3)*a(n-5)
+2*(-2*n+5)*a(n-6) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - x^2*c)*(1 - x - x^2) = 1;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (-5)*(54) + (24)*(23) + (-28)*(11) + (-10)*(5) + (33)*(3) + (-9)*(1) + (-14)*(1) = 0.
-/

namespace OMA.S_oeis_a139376

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A139376, for n ≥ 6. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * ((1 - X ^ 2 * c) * (1 - X - X ^ 2)) = 1 →
    ∀ n : ℕ, 6 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-12 + 6 * (n : ℚ)) * coeff (n - 1) G +
        (20 - 8 * (n : ℚ)) * coeff (n - 2) G + (2 - 2 * (n : ℚ)) * coeff (n - 3) G +
        (-21 + 9 * (n : ℚ)) * coeff (n - 4) G + (9 - 3 * (n : ℚ)) * coeff (n - 5) G +
        (10 - 4 * (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a139376
