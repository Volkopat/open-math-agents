import Mathlib

/-!
# A106272: Mathar's recurrence

Source: https://oeis.org/A106272
Credit: @ivillar

Status: known result. The comments of the entry record a proof of Mathar's conjecture from the g.f.
(Petros Hadjicostas, Jul 15 2019).

A106272 (offset 0): antidiagonal sums of number triangle A106270;
data 1, -1, -1, -6, -15, -48, -147, -477, -1577, -5339, -18373, -64125, ...

Conjecture (R. J. Mathar, Nov 09 2012):
(n+1)*a(n) + 2*(1-2*n)*a(n-1) - (n+1)*a(n-2) + 2*(2*n-1)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the Catalan g.f., determined by
2*x*c = 1 - S; and the g.f. G = c(x)*sqrt(1-4x)/(1-x^2) is determined by G*(1 - x^2) = c*S;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (4)*(-6) + (-10)*(-1) + (-4)*(-1) + (10)*(1) = 0.
-/

namespace OMA.S_oeis_a106272

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A106272, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - X ^ 2) = c * S →
    ∀ n : ℕ, 3 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 - 4 * (n : ℚ)) * coeff (n - 1) G +
        (-1 - (n : ℚ)) * coeff (n - 2) G + (-2 + 4 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a106272
