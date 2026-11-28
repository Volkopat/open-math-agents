import Mathlib

/-!
# A104625: Mathar's recurrence

Source: https://oeis.org/A104625
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A104625 (offset 0): expansion of 1/(sqrt(1-4*x) - x^2);
data 1, 2, 7, 24, 87, 322, 1211, 4604, 17645, 68042, 263655, 1025632, ...

Conjecture (R. J. Mathar, Feb 20 2015):
n*a(n) + (n-3)*a(n-1) + 2*(-28*n+51)*a(n-2) + 72*(2*n-5)*a(n-3) - n*a(n-4) + (-5*n+3)*a(n-5) +
18*(2*n-5)*a(n-6) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(S - x^2) = 1;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (6)*(1211) + (3)*(322) + (-234)*(87) + (504)*(24) + (-6)*(7) + (-27)*(2) + (126)*(1) = 0.
-/

namespace OMA.S_oeis_a104625

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A104625, for n ≥ 6. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * (S - X ^ 2) = 1 →
    ∀ n : ℕ, 6 ≤ n →
      ((n : ℚ)) * coeff n G + (-3 + (n : ℚ)) * coeff (n - 1) G +
        (102 - 56 * (n : ℚ)) * coeff (n - 2) G + (-360 + 144 * (n : ℚ)) * coeff (n - 3) G +
        (-(n : ℚ)) * coeff (n - 4) G + (3 - 5 * (n : ℚ)) * coeff (n - 5) G +
        (-90 + 36 * (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a104625
