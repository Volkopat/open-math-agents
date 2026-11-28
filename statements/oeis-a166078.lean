import Mathlib

/-!
# A166078: Mathar's recurrence

Source: https://oeis.org/A166078
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A166078 (offset 0): expansion of (3(1-x)-sqrt(1+6x-7x^2))/(2(1-x)(1-2x));
data 1, 0, 2, -6, 30, -150, 806, -4494, 25822, -151782, 908502, -5518590, ...

Conjecture (R. J. Mathar, Nov 14 2011):
n*a(n) + 2*(2*n - 5)*a(n - 1) + (34 - 19*n)*a(n - 2) + 14*(n - 2)*a(n - 3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1+6*x-7*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*(1 - x)*(1 - 2*x)*G = 3*(1 - x) - S;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (3)*(-6) + (2)*(2) + (-23)*(0) + (14)*(1) = 0.
-/

namespace OMA.S_oeis_a166078

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A166078, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 + 6 * X - 7 * X ^ 2 →
    coeff 0 S = 1 →
    2 * (1 - X) * (1 - 2 * X) * G = 3 * (1 - X) - S →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ)) * coeff n G + (-10 + 4 * (n : ℚ)) * coeff (n - 1) G +
        (34 - 19 * (n : ℚ)) * coeff (n - 2) G + (-28 + 14 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a166078
