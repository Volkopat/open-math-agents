import Mathlib

/-!
# A171849: Mathar's recurrence

Source: https://oeis.org/A171849
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A171849 (offset 0): total area under all the level steps in all peakless Motzkin paths of length n (n>=0);
data 0, 0, 0, 1, 4, 12, 36, 104, 292, 810, 2224, 6058, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+1)*a(n) -5*n*a(n-1) +(7*n-11)*a(n-2) +2*(-3*n+10)*a(n-3) +(13*n-31)*a(n-4) +11*(-n+4)*a(n-5)
+(13*n-73)*a(n-6) +2*(-3*n+14)*a(n-7) +(7*n-45)*a(n-8) +5*(-n+8)*a(n-9) +(n-9)*a(n-10) = 0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T*(T-1) (this
equation has exactly one power series solution, with constant term 1; it is the g.f. of the peakless
Motzkin paths); and the g.f. G is determined by
G*(1 + x + x^2)*(1 - 3*x + x^2) = x^3*T^2;
a(n) = [x^n] G. The recurrence involves a(n-10), so it is stated for n ≥ 10; it is checked by the data, for
example at n = 10: (11)*(2224) + (-50)*(810) + (59)*(292) + (-40)*(104) + (99)*(36) + (-66)*(12) + (57)*(4) + (-32)*(1) + (25)*(0) + (-10)*(0) + (1)*(0) = 0.
-/

namespace OMA.S_oeis_a171849

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A171849, for n ≥ 10. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T * (T - 1) →
    G * ((1 + X + X ^ 2) * (1 - 3 * X + X ^ 2)) = X ^ 3 * T ^ 2 →
    ∀ n : ℕ, 10 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (-5 * (n : ℚ)) * coeff (n - 1) G +
        (-11 + 7 * (n : ℚ)) * coeff (n - 2) G + (20 - 6 * (n : ℚ)) * coeff (n - 3) G +
        (-31 + 13 * (n : ℚ)) * coeff (n - 4) G + (44 - 11 * (n : ℚ)) * coeff (n - 5) G +
        (-73 + 13 * (n : ℚ)) * coeff (n - 6) G + (28 - 6 * (n : ℚ)) * coeff (n - 7) G +
        (-45 + 7 * (n : ℚ)) * coeff (n - 8) G + (40 - 5 * (n : ℚ)) * coeff (n - 9) G +
        (-9 + (n : ℚ)) * coeff (n - 10) G = 0 := by
  sorry

end OMA.S_oeis_a171849
