import Mathlib

/-!
# A166076: Mathar's recurrence

Source: https://oeis.org/A166076
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A166076 (offset 0): expansion of (7+5x-sqrt(1-10x-7x^2))/(2(3+5x+2x^2));
data 1, 0, 2, 10, 70, 530, 4278, 36050, 313558, 2793970, 25374262, 234016530, ...

Conjecture (R. J. Mathar, Feb 10 2015): D-finite with recurrence
3*(n)*a(n) + 5*(-5*n + 9)*a(n - 1) + 69*(-n + 2)*a(n - 2) + 5*(-11*n + 27)*a(n - 3) + 14*(-n +
3)*a(n - 4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-10*x-7*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*(3 + 5*x + 2*x^2)*G = 7 + 5*x - S;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (12)*(70) + (-55)*(10) + (-138)*(2) + (-85)*(0) + (-14)*(1) = 0.
-/

namespace OMA.S_oeis_a166076

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A166076, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 10 * X - 7 * X ^ 2 →
    coeff 0 S = 1 →
    2 * (3 + 5 * X + 2 * X ^ 2) * G = 7 + 5 * X - S →
    ∀ n : ℕ, 4 ≤ n →
      (3 * (n : ℚ)) * coeff n G + (45 - 25 * (n : ℚ)) * coeff (n - 1) G +
        (138 - 69 * (n : ℚ)) * coeff (n - 2) G + (135 - 55 * (n : ℚ)) * coeff (n - 3) G +
        (42 - 14 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a166076
