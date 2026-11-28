import Mathlib

/-!
# A116388: Mathar's recurrence

Source: https://oeis.org/A116388
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A116388 (offset 0): expansion of 1/((1+x*(1-M(x)))*sqrt(1-2*x-3*x^2)), M(x) the g.f. of A001006;
data 1, 1, 4, 10, 29, 82, 236, 681, 1975, 5745, 16757, 48982, ...

Conjecture (R. J. Mathar, Jun 22 2016):
n*a(n) + 7*(-n+1)*a(n-1) + 2*(4*n-9)*a(n-2) + (25*n-58)*a(n-3) + (-18*n+65)*a(n-4)
+ (-52*n+199)*a(n-5) + (-31*n+135)*a(n-6) + 6*(-n+5)*a(n-7) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-2*x-3*x^2 and constant term 1, that is
S = sqrt(1-2x-3x^2) (the constant term selects the branch of the square root); M is the Motzkin g.f.,
determined by 2*x^2*M = 1 - x - S; and the g.f. G is determined by G*(1 + x*(1-M))*S = 1;
a(n) = [x^n] G. The recurrence involves a(n-7), so it is stated for n ≥ 7; it is checked by the data, for
example at n = 7: (7)*(681) + (-42)*(236) + (38)*(82) + (117)*(29) + (-61)*(10) + (-165)*(4) + (-82)*(1) + (-12)*(1) = 0.
-/

namespace OMA.S_oeis_a116388

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A116388, for n ≥ 7. -/
theorem main : ∀ S M G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X ^ 2 * M = 1 - X - S →
    G * ((1 + X * (1 - M)) * S) = 1 →
    ∀ n : ℕ, 7 ≤ n →
      ((n : ℚ)) * coeff n G + (7 - 7 * (n : ℚ)) * coeff (n - 1) G +
        (-18 + 8 * (n : ℚ)) * coeff (n - 2) G + (-58 + 25 * (n : ℚ)) * coeff (n - 3) G +
        (65 - 18 * (n : ℚ)) * coeff (n - 4) G + (199 - 52 * (n : ℚ)) * coeff (n - 5) G +
        (135 - 31 * (n : ℚ)) * coeff (n - 6) G + (30 - 6 * (n : ℚ)) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a116388
