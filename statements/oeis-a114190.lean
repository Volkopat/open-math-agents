import Mathlib

/-!
# A114190: Mathar's recurrence

Source: https://oeis.org/A114190
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A114190 (offset 0): expansion of 1/(1+x*(1-x)*c(-2*x)), c(x) the g.f. of A000108;
data 1, -1, 4, -17, 87, -490, 2945, -18517, 120340, -802005, 5451651, -37652546, ...

Conjecture (R. J. Mathar, Dec 10 2011):
n*a(n) + (7*n-10)*a(n-1) + 2*(14-3*n)*a(n-2) + (13*n-20)*a(n-3) + (66-23*n)*a(n-4) +
4*(2*n-7)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1+8*x and constant term 1, that is S = sqrt(1+8x)
(the constant term selects the branch of the square root); c is the series c(-2x), with c(x) the Catalan
g.f., determined by -4*x*c = 1 - S; and the g.f. G is determined by G*(1 + x*(1-x)*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (5)*(-490) + (25)*(87) + (-2)*(-17) + (45)*(4) + (-49)*(-1) + (12)*(1) = 0.
-/

namespace OMA.S_oeis_a114190

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A114190, for n ≥ 5. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 + 8 * X →
    coeff 0 S = 1 →
    -(4 * X * c) = 1 - S →
    G * (1 + X * (1 - X) * c) = 1 →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * coeff n G + (-10 + 7 * (n : ℚ)) * coeff (n - 1) G +
        (28 - 6 * (n : ℚ)) * coeff (n - 2) G + (-20 + 13 * (n : ℚ)) * coeff (n - 3) G +
        (66 - 23 * (n : ℚ)) * coeff (n - 4) G + (-28 + 8 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a114190
