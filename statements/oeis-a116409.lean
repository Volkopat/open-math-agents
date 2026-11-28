import Mathlib

/-!
# A116409: Mathar's recurrence

Source: https://oeis.org/A116409
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A116409 (offset 0): expansion of (1-x-2x^2+sqrt(1-2x-3x^2))/(2(1-x)(1-2x-3x^2));
data 1, 2, 5, 13, 36, 102, 294, 855, 2502, 7352, 21670, 64021, ...

Conjecture (R. J. Mathar, Nov 11 2014): D-finite with recurrence
n*a(n) + 2*(-3*n + 2)*a(n - 1) + 2*(4*n - 5)*a(n - 2) + 6*(n - 2)*a(n - 3) + 9*(-n + 2)*a(n - 4) =
0.

Formalization: S is the formal power series over ℚ with S^2 = 1-2*x-3*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*(1 - x)*(1 - 2*x - 3*x^2)*G = 1 - x - 2*x^2 + S;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (4)*(36) + (-20)*(13) + (22)*(5) + (12)*(2) + (-18)*(1) = 0.
-/

namespace OMA.S_oeis_a116409

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A116409, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    2 * (1 - X) * (1 - 2 * X - 3 * X ^ 2) * G = 1 - X - 2 * X ^ 2 + S →
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ)) * coeff n G + (4 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-10 + 8 * (n : ℚ)) * coeff (n - 2) G + (-12 + 6 * (n : ℚ)) * coeff (n - 3) G +
        (18 - 9 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a116409
