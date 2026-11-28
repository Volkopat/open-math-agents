import Mathlib

/-!
# A226751: Mathar's recurrence

Source: https://oeis.org/A226751
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A226751 (offset 0): g.f.: 1 / (1 + 6*x*G(x) - 7*x*G(x)^2), where G(x) = 1 + x*G(x)^3 is the g.f. of A001764;
data 1, 1, 9, 48, 289, 1761, 10932, 68664, 435201, 2777763, 17829489, 114968052, ...

Conjecture (R. J. Mathar, Jun 14 2016):
18*n*(2*n-1)*(55*n-76)*a(n) +(-11605*n^3+28521*n^2-20870*n+4536)*a(n-1)
-24*(55*n-21)*(3*n-4)*(3*n-2)*a(n-2) = 0.

Formalization: T is the g.f. of A001764, the formal power series over ℚ with T = 1 + x*T^3 (this equation determines
T, and its constant term is 1), and the g.f. G is determined by G*(1 + 6*x*T - 7*x*T^2) = 1;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (3672)*(9) + (-15960)*(1) + (-17088)*(1) = 0.
-/

namespace OMA.S_oeis_a226751

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A226751, for n ≥ 2. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T ^ 3 →
    G * (1 + 6 * X * T - 7 * X * T ^ 2) = 1 →
    ∀ n : ℕ, 2 ≤ n →
      (1368 * (n : ℚ) - 3726 * (n : ℚ) ^ 2 + 1980 * (n : ℚ) ^ 3) * coeff n G + (4536 - 20870 * (n : ℚ) + 28521 * (n : ℚ) ^ 2 - 11605 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (4032 - 19632 * (n : ℚ) + 28296 * (n : ℚ) ^ 2 - 11880 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a226751
