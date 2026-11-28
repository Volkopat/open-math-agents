import Mathlib

/-!
# A185966: Mathar's recurrence

Source: https://oeis.org/A185966
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Nov 15 2012); the entry records it as a conjecture and notes no proof or
verification of it.

A185966 (offset 0): series reversion of A028310;
data 1, -1, 0, 2, -2, -5, 14, 5, -72, 68, 278, -726, ...

Conjecture (R. J. Mathar, Nov 15 2012):
6*n*(n+1)*a(n) -n*(n-14)*a(n-1) +2*n*(14*n-19)*a(n-2) -4*(n-2)*(17*n-48)*a(n-3)
+6*(2*n-5)*(n-4)*a(n-4) = 0.

Formalization: A028310 is 1, 1, 2, 3, 4, 5, ... with g.f. (1 - x + x^2)/(1 - x)^2, and the sequence is the series reversion of
x*(1 - x + x^2)/(1 - x)^2 divided by x (offset 0). T is that reversion: the formal power series over ℚ with
constant term 0 and T*(1 - T + T^2) = x*(1 - T)^2, that is T*(1 - T + T^2)/(1 - T)^2 = x (this is the
equation B = (1 - B)*(x + B*(B - x)) recorded in the entry by Michael Somos for B(x) = x*A(x)); and the
g.f. G is determined by x*G = T (its constant term 1 is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (120)*(-2) + (40)*(2) + (296)*(0) + (-160)*(-1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a185966

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A185966, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, coeff 0 T = 0 →
    T * (1 - T + T ^ 2) = X * (1 - T) ^ 2 →
    X * G = T →
    coeff 0 G = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (6 * (n : ℚ) + 6 * (n : ℚ) ^ 2) * coeff n G + (14 * (n : ℚ) - (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-38 * (n : ℚ) + 28 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-384 + 328 * (n : ℚ) - 68 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (120 - 78 * (n : ℚ) + 12 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a185966
