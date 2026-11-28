import Mathlib

/-!
# A220898: Mathar's recurrence

Source: https://oeis.org/A220898
Credit: @ivillar

Status: open conjecture (R. J. Mathar, May 30 2014); the entry records it as a conjecture and notes no proof or
verification of it.

A220898 (offset 0): number of primitive maps on n edges;
data 2, 1, 1, 3, 9, 32, 122, 494, 2088, 9130, 41018, 188420, ...

Conjecture (R. J. Mathar, May 30 2014):
2*(n+1)*(2*n+1)*a(n) +(-15*n^2+19*n-8)*a(n-1) -2*(21*n-22)*(n-2)*a(n-2) -23*(n-2)*(n-3)*a(n-3) = 0.

Formalization: The entry gives the g.f. A(x/(1+x)), where A(x) is the g.f. of A000139, and A000139 records the o.g.f.
A(x) = T(x)*(3 - T(x)), where T(x) = 1 + x*T(x)^3 is the o.g.f. of A001764 (Peter Bala, Feb 05 2022); this
is used as the definition here. Substituting x/(1+x) for x, the series T = T(x/(1+x)) is the formal power
series over ℚ with T = 1 + (x/(1+x))*T^3, written as (1+x)*T = (1+x) + x*T^3 (this equation has exactly one
power series solution, with constant term 1); and the g.f. is G = T*(3 - T) (its constant term 2 is
recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (56)*(3) + (-86)*(1) + (-82)*(1) + (0)*(2) = 0.
-/

namespace OMA.S_oeis_a220898

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A220898, for n ≥ 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, (1 + X) * T = (1 + X) + X * T ^ 3 →
    G = T * (3 - T) →
    coeff 0 G = 2 →
    ∀ n : ℕ, 3 ≤ n →
      (2 + 6 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (-8 + 19 * (n : ℚ) - 15 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-88 + 128 * (n : ℚ) - 42 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-138 + 115 * (n : ℚ) - 23 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a220898
