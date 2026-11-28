import Mathlib

/-!
# A138164: Mathar's recurrence

Source: https://oeis.org/A138164
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A138164 (offset 0): row sums of Riordan array (c(-x^2),xc(-x^2)^2)^(-1) where c(x) is the g.f. of A000108;
data 1, 1, 2, 4, 9, 20, 47, 109, 262, 622, 1516, 3653, ...

Conjecture (R. J. Mathar, Feb 24 2015):
-8*n*(n-1)*a(n) + 12*(n+3)*(n-1)*a(n-1) + 2*(89*n^2-512*n+651)*a(n-2) +
3*(-127*n^2+715*n-966)*a(n-3) + 3*(-247*n^2+2431*n-5698)*a(n-4) + 9*(75*n-341)*(3*n-16)*a(n-5) -
72*(3*n-14)*(3*n-16)*a(n-6) = 0.

Formalization: The entry gives the g.f. as 1/(1-v-v^2), where v is the series reversion of x*(1-x^2), and this is used
as the definition here: T (the v of the entry) is the formal power series over ℚ with zero constant
term and T - T^3 = x (the constant term selects the reversion among the three series solutions), and
G is determined by G*(1 - T - T^2) = 1;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (-240)*(47) + (540)*(20) + (1566)*(9) + (-3744)*(4) + (-12)*(2) + (1962)*(1) + (-576)*(1) = 0.
-/

namespace OMA.S_oeis_a138164

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A138164, for n ≥ 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, T - T ^ 3 = X →
    coeff 0 T = 0 →
    G * (1 - T - T ^ 2) = 1 →
    ∀ n : ℕ, 6 ≤ n →
      (8 * (n : ℚ) - 8 * (n : ℚ) ^ 2) * coeff n G + (-36 + 24 * (n : ℚ) + 12 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (1302 - 1024 * (n : ℚ) + 178 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-2898 + 2145 * (n : ℚ) - 381 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-17094 + 7293 * (n : ℚ) - 741 * (n : ℚ) ^ 2) * coeff (n - 4) G + (49104 - 20007 * (n : ℚ) + 2025 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (-16128 + 6480 * (n : ℚ) - 648 * (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a138164
