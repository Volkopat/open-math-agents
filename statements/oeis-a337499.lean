import Mathlib

/-!
# A337499: Mathar's recurrence

Source: https://oeis.org/A337499
Credit: @ivillar

Status: known result. The entry records the recurrence as conjectured by R. J. Mathar, Sep 27 2020, and verified by
Robert Israel, Oct 08 2020.

A337499 (offset 0): a(n) is the number of ballot sequences of length n tied or won by at most 2 votes;
data 1, 2, 4, 6, 14, 20, 50, 70, 182, 252, 672, 924, ...

Conjecture (R. J. Mathar, Sep 27 2020): D-finite with recurrence
(n+2)*a(n) +n*a(n-1) +(-5*n-2)*a(n-2) +4*(-n+1)*a(n-3) +4*(n-3)*a(n-4) = 0.

Formalization: The entry gives the g.f. in closed form,
((4*x + 2)*sqrt(1-4*x^2) + 4*x^2 + 4*x + 2)/(sqrt(1-4*x^2)*(1 + sqrt(1-4*x^2))^2) (Robert Israel, Oct 08 2020),
and this closed form is used as the definition here. S is the formal power series over ℚ with
S^2 = 1-4*x^2 and constant term 1 (the constant term selects the branch of the square root), and G is
determined by S*(1+S)^2*G = (4*x+2)*S + 4*x^2 + 4*x + 2;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (6)*(14) + (4)*(6) + (-22)*(4) + (-12)*(2) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a337499

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A337499, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    S * (1 + S) ^ 2 * G = (4 * X + 2) * S + 4 * X ^ 2 + 4 * X + 2 →
    ∀ n : ℕ, 4 ≤ n →
      (2 + (n : ℚ)) * coeff n G + ((n : ℚ)) * coeff (n - 1) G +
        (-2 - 5 * (n : ℚ)) * coeff (n - 2) G + (4 - 4 * (n : ℚ)) * coeff (n - 3) G +
        (-12 + 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a337499
