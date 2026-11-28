import Mathlib

/-!
# A182881: Mathar's recurrence

Source: https://oeis.org/A182881
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A182881 (offset 0): number of (1,1)-steps in all weighted lattice paths in L_n;
data 0, 0, 0, 2, 6, 18, 56, 162, 462, 1306, 3648, 10116, ...

Conjecture (R. J. Mathar, Jun 14 2016):
(-n+3)*a(n) +(2*n-5)*a(n-1) +(n-2)*a(n-2) +(2*n-3)*a(n-3) +(-n+1)*a(n-4) = 0.

Formalization: the entry gives the g.f. in closed form, 2*z^3/[(1-3*z+z^2)*(1+z+z^2)]^(3/2), and
this closed form is used as the definition here. S is the formal power series over ℚ with
S^2 = (1-3*x+x^2)*(1+x+x^2) = 1 - 2x - x^2 - 2x^3 + x^4 and constant term 1 (the constant term
selects the branch of the square root), so that the 3/2 power is (1-3x+x^2)*(1+x+x^2)*S, and the
g.f. G is determined by (1 - 3*x + x^2)*(1 + x + x^2)*S*G = 2*x^3;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-1)*(6) + (3)*(2) + (2)*(0) + (5)*(0) + (-3)*(0) = 0.
-/

namespace OMA.S_oeis_a182881

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A182881, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    (1 - 3 * X + X ^ 2) * (1 + X + X ^ 2) * S * G = 2 * X ^ 3 →
    ∀ n : ℕ, 4 ≤ n →
      (3 - (n : ℚ)) * coeff n G + (-5 + 2 * (n : ℚ)) * coeff (n - 1) G +
        (-2 + (n : ℚ)) * coeff (n - 2) G + (-3 + 2 * (n : ℚ)) * coeff (n - 3) G +
        (1 - (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a182881
