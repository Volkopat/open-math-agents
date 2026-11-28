import Mathlib

/-!
# A025577: Mathar's recurrence

Source: https://oeis.org/A025577
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A025577 (offset 1): expansion of (x/(1-x))*sqrt((1+x)/(1-3*x));
data 1, 3, 7, 17, 43, 113, 305, 839, 2339, 6585, 18677, 53283, ...

Conjecture (R. J. Mathar, Jul 02 2018): D-finite with recurrence
(-n + 1)*a(n) + 3*(n - 1)*a(n - 1) + (n - 7)*a(n - 2) + 3*(-n + 3)*a(n - 3) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-3*x) = 1+x and constant term 1, that is
T = sqrt((1+x)/(1-3x)) (the constant term selects the branch of the square root), and the g.f. G is
determined by G*(1-x) = x*T;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (-2)*(7) + (6)*(3) + (-4)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a025577

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A025577, for n ≥ 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - 3 * X) = 1 + X →
    coeff 0 T = 1 →
    G * (1 - X) = X * T →
    ∀ n : ℕ, 3 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-3 + 3 * (n : ℚ)) * coeff (n - 1) G +
        (-7 + (n : ℚ)) * coeff (n - 2) G + (9 - 3 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a025577
