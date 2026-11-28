import Mathlib

/-!
# A247374: Mathar's recurrence

Source: https://oeis.org/A247374
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Nov 19 2019); the entry records it as a conjecture and notes no proof or
verification of it.

A247374 (offset 1): number of button presses required to try every combination of a binary combination lock with n number buttons;
data 3, 8, 17, 38, 77, 165, 331, 698, 1397, 2921, 5843, 12149, ...

Conjecture (R. J. Mathar, Nov 19 2019): D-finite with recurrence
n*a(n) +2*(-2*n+1)*a(n-1) +(n-2)*a(n-2) +2*(7*n-10)*a(n-3) +4*(-5*n+11)*a(n-4) +8*(n-3)*a(n-5) = 0.

Formalization: the entry gives a(n) = A000079(n) + A014495(n) + A014314(n) (the numbers of presses of the try button, of
the clear button and of the number buttons), and this formula is used as the definition here, through the
generating functions of the three sequences: 1/(1-2*x) for A000079(n) = 2^n; the g.f.
(x+1)/(2*x*(x-1)) - sqrt(1-4*x^2)/(2*x*(2*x-1)) recorded in A014495 (central binomial coefficient - 1; Robert
Israel, Feb 11 2018); and the g.f. (1-q)*(z+q)/(2*z*q*(1-2*z)), q = sqrt(1-4*z^2), recorded in A014314. S is
the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1 (the constant term selects the branch
of the square root); A is determined by 2*x*(x-1)*(2*x-1)*A = (x+1)*(2*x-1) - (x-1)*S and B by
2*x*S*(1-2*x)*B = (1-S)*(x+S) (the two stated expressions multiplied by their denominators, which are
nonzero power series); and G is determined by (1-2*x)*G = 1 + (1-2*x)*(A + B), that is
G = 1/(1-2*x) + A + B. The sequence has offset 1; the coefficient [x^0] G = 1 is the value
2^0 + A014495(0) + A014314(0) of the same formula at n = 0, and it enters the instance n = 5 of main;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (5)*(77) + (-18)*(38) + (3)*(17) + (50)*(8) + (-56)*(3) + (16)*(1) = 0.
-/

namespace OMA.S_oeis_a247374

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A247374, for n ≥ 5. -/
theorem main : ∀ S A B G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X * (X - 1) * (2 * X - 1) * A = (X + 1) * (2 * X - 1) - (X - 1) * S →
    2 * X * S * (1 - 2 * X) * B = (1 - S) * (X + S) →
    (1 - 2 * X) * G = 1 + (1 - 2 * X) * (A + B) →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * coeff n G + (2 - 4 * (n : ℚ)) * coeff (n - 1) G +
        (-2 + (n : ℚ)) * coeff (n - 2) G + (-20 + 14 * (n : ℚ)) * coeff (n - 3) G +
        (44 - 20 * (n : ℚ)) * coeff (n - 4) G + (-24 + 8 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a247374
