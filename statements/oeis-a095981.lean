import Mathlib

/-!
# A095981: Mathar's recurrence

Source: https://oeis.org/A095981
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A095981 (offset 0): number of plateau-free Motzkin paths of length n;
data 0, 0, 1, 2, 5, 11, 26, 61, 147, 357, 879, 2183, ...

Conjecture (R. J. Mathar, Nov 23 2014):
(n+2)*a(n) +(-5*n-4)*a(n-1) +6*n*a(n-2) +(4*n-13)*a(n-3) +(-13*n+43)*a(n-4) +3*(3*n-13)*a(n-5)
+(-n+4)*a(n-6) +(-n+7)*a(n-7) = 0.

Formalization: the entry gives the g.f. in closed form,
(-1 + 2*x + x^2 - x^3 + (1 - 4*x + 2*x^2 + 6*x^3 - 7*x^4 + 2*x^5 + x^6)^(1/2))/(2*(-1 + x)*x^2),
and this closed form is used as the definition here. S is the formal power series over ℚ with
S^2 = 1 - 4*x + 2*x^2 + 6*x^3 - 7*x^4 + 2*x^5 + x^6 and constant term 1 (the constant term selects
the branch of the square root), and the g.f. G is determined by
2*(-1 + x)*x^2*G = -1 + 2*x + x^2 - x^3 + S;
a(n) = [x^n] G. The recurrence involves a(n-7), so it is stated for n ≥ 7; it is checked by the data, for
example at n = 7: (9)*(61) + (-39)*(26) + (42)*(11) + (15)*(5) + (-48)*(2) + (24)*(1) + (-3)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a095981

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A095981, for n ≥ 7. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X + 2 * X ^ 2 + 6 * X ^ 3 - 7 * X ^ 4 + 2 * X ^ 5 + X ^ 6 →
    coeff 0 S = 1 →
    2 * (-1 + X) * X ^ 2 * G = -1 + 2 * X + X ^ 2 - X ^ 3 + S →
    ∀ n : ℕ, 7 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-4 - 5 * (n : ℚ)) * coeff (n - 1) G +
        (6 * (n : ℚ)) * coeff (n - 2) G + (-13 + 4 * (n : ℚ)) * coeff (n - 3) G +
        (43 - 13 * (n : ℚ)) * coeff (n - 4) G + (-39 + 9 * (n : ℚ)) * coeff (n - 5) G +
        (4 - (n : ℚ)) * coeff (n - 6) G + (7 - (n : ℚ)) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a095981
