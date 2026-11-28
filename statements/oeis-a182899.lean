import Mathlib

/-!
# A182899: Mathar's recurrence

Source: https://oeis.org/A182899
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A182899 (offset 0): number of returns to the horizontal axis (both from above and below) in all weighted lattice paths in L_n;
data 0, 0, 0, 2, 6, 18, 54, 152, 422, 1160, 3156, 8534, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
n*a(n) +(-4*n+3)*a(n-1) +(2*n-3)*a(n-2) +11*(n-3)*a(n-4) +(2*n-9)*a(n-6) +(-4*n+21)*a(n-7)
+(n-6)*a(n-8) = 0.

Formalization: T is the series c of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T + x^3*T^2
(this equation has exactly one power series solution, with constant term 1); and the g.f. G is
determined by G*(1 + x + x^2)*(1 - 3*x + x^2) = 2*x^3*T;
a(n) = [x^n] G. The recurrence involves a(n-8), so it is stated for n ≥ 8; it is checked by the data, for
example at n = 8: (8)*(422) + (-29)*(152) + (13)*(54) + (55)*(6) + (7)*(0) + (-11)*(0) + (2)*(0) = 0.
-/

namespace OMA.S_oeis_a182899

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A182899, for n ≥ 8. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T + X ^ 3 * T ^ 2 →
    G * ((1 + X + X ^ 2) * (1 - 3 * X + X ^ 2)) = 2 * X ^ 3 * T →
    ∀ n : ℕ, 8 ≤ n →
      ((n : ℚ)) * coeff n G + (3 - 4 * (n : ℚ)) * coeff (n - 1) G +
        (-3 + 2 * (n : ℚ)) * coeff (n - 2) G + (-33 + 11 * (n : ℚ)) * coeff (n - 4) G +
        (-9 + 2 * (n : ℚ)) * coeff (n - 6) G + (21 - 4 * (n : ℚ)) * coeff (n - 7) G +
        (-6 + (n : ℚ)) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a182899
