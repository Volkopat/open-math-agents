import Mathlib

/-!
# A117186: Mathar's recurrence

Source: https://oeis.org/A117186
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A117186 (offset 0): expansion of (1+x)c(x^2)/((1-xc(x^2))*sqrt(1-4x^2)), c(x) the g.f. of A000108;
data 1, 2, 5, 9, 21, 38, 86, 157, 349, 642, 1410, 2610, ...

Conjecture (R. J. Mathar, Nov 15 2011):
-(n+1)*a(n) +(n+1)*a(n-1) +2*(3*n-2)*a(n-2) -4*n*a(n-3) +8*(3-n)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1, that is S = sqrt(1-4x^2)
(the constant term selects the branch of the square root); c is the series c(x^2), with c(x) the Catalan
g.f., determined by 2*x^2*c = 1 - S; and the g.f. G is determined by G*(1 - x*c)*S = (1+x)*c;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-5)*(21) + (5)*(9) + (20)*(5) + (-16)*(2) + (-8)*(1) = 0.
-/

namespace OMA.S_oeis_a117186

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A117186, for n ≥ 4. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X ^ 2 * c = 1 - S →
    G * ((1 - X * c) * S) = (1 + X) * c →
    ∀ n : ℕ, 4 ≤ n →
      (-1 - (n : ℚ)) * coeff n G + (1 + (n : ℚ)) * coeff (n - 1) G +
        (-4 + 6 * (n : ℚ)) * coeff (n - 2) G + (-4 * (n : ℚ)) * coeff (n - 3) G +
        (24 - 8 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a117186
