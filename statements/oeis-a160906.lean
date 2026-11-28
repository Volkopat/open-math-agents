import Mathlib

/-!
# A160906: Mathar's recurrence

Source: https://oeis.org/A160906
Credit: @ivillar

Status: known result. The entry records: R. J. Mathar's conjecture verified using differential equation (2112*x + 2)*y +
(11328*x^2 - 842*x + 2)*y' + (7776*x^3 - 1319*x^2 + 34*x)*y'' + (1080*x^4 - 295*x^3 + 20*x^2)*y'''
- 12 satisfied by the g.f. y(x). - Robert Israel, Mar 13 2026

A160906 (offset 0): row sums of A159841;
data 1, 5, 29, 176, 1093, 6885, 43796, 280600, 1807781, 11698223, 75973189, 494889092, ...

Conjecture (R. J. Mathar, Jul 20 2016):
2*n*(2*n-1)*(5*n-4)*a(n) +(-295*n^3+451*n^2-130*n-24)*a(n-1) +24*(5*n+1)*(3*n-4)*(3*n-2)*a(n-2) =
0.

Formalization: The entry gives the g.f. g^2/((2-g)*(3-2*g)) where g = 1 + x*g^3 is the g.f. of A001764 (Seiichi Manyama,
Aug 12 2025), and this is used as the definition here. T (the g of the entry) is the formal power
series over ℚ with T = 1 + x*T^3 (this equation has exactly one power series solution, with constant
term 1); and G is determined by G*(2-T)*(3-2*T) = T^2 (its constant term 1 is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (72)*(29) + (-840)*(5) + (2112)*(1) = 0.
-/

namespace OMA.S_oeis_a160906

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A160906, for n ≥ 2. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T ^ 3 →
    G * ((2 - T) * (3 - 2 * T)) = T ^ 2 →
    coeff 0 G = 1 →
    ∀ n : ℕ, 2 ≤ n →
      (8 * (n : ℚ) - 26 * (n : ℚ) ^ 2 + 20 * (n : ℚ) ^ 3) * coeff n G + (-24 - 130 * (n : ℚ) + 451 * (n : ℚ) ^ 2 - 295 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (192 + 528 * (n : ℚ) - 1944 * (n : ℚ) ^ 2 + 1080 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a160906
