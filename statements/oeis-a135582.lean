import Mathlib

/-!
# A135582: Mathar's recurrence

Source: https://oeis.org/A135582
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A135582 (offset 0): expansion of 1/((1-x^2*c(x))(1-x-2x^2)) where c(x) is the g.f. of A000108;
data 1, 1, 4, 7, 18, 39, 95, 232, 606, 1663, 4839, 14807, ...

Conjecture (R. J. Mathar, Feb 23 2015):
(-n+1)*a(n) +6*(n-2)*a(n-1) +(-7*n+19)*a(n-2) +(-7*n+13)*a(n-3) +(13*n-31)*a(n-4) +2*(-n+4)*a(n-5)
+4*(-2*n+5)*a(n-6) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - x^2*c)*(1 - x - 2*x^2) = 1;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (-5)*(95) + (24)*(39) + (-23)*(18) + (-29)*(7) + (47)*(4) + (-4)*(1) + (-28)*(1) = 0.
-/

namespace OMA.S_oeis_a135582

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A135582, for n ≥ 6. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * ((1 - X ^ 2 * c) * (1 - X - 2 * X ^ 2)) = 1 →
    ∀ n : ℕ, 6 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-12 + 6 * (n : ℚ)) * coeff (n - 1) G +
        (19 - 7 * (n : ℚ)) * coeff (n - 2) G + (13 - 7 * (n : ℚ)) * coeff (n - 3) G +
        (-31 + 13 * (n : ℚ)) * coeff (n - 4) G + (8 - 2 * (n : ℚ)) * coeff (n - 5) G +
        (20 - 8 * (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a135582
