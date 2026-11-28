import Mathlib

/-!
# A106271: Mathar's recurrence

Source: https://oeis.org/A106271
Credit: @ivillar

Status: known result. The comments of the entry record a proof of Mathar's conjecture from the g.f. (Petros
Hadjicostas, Jul 15 2019).

A106271 (offset 0): row sums of number triangle A106270;
data 1, 0, -2, -7, -21, -63, -195, -624, -2054, -6916, -23712, -82498, ...

Conjecture (R. J. Mathar, Nov 09 2012):
(n+1)*a(n) + (1-5*n)*a(n-1) + 2*(2*n-1)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the Catalan g.f., determined by
2*x*c = 1 - S; and the g.f. G = c(x)*sqrt(1-4x)/(1-x) is determined by G*(1 - x) = c*S;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (3)*(-2) + (-9)*(0) + (6)*(1) = 0.
-/

namespace OMA.S_oeis_a106271

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A106271, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - X) = c * S →
    ∀ n : ℕ, 2 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (1 - 5 * (n : ℚ)) * coeff (n - 1) G +
        (-2 + 4 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a106271
