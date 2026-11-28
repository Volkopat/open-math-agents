import Mathlib

/-!
# A154623: Mathar's recurrence

Source: https://oeis.org/A154623
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A154623 (offset 0): expansion of 1+(x/(1-5*x))*c(x/(1-5*x)) where c(x) is the g.f. of A000108;
data 1, 1, 6, 37, 235, 1539, 10392, 72267, 516474, 3783115, 28317562, 215969271, ...

Conjecture (R. J. Mathar, Dec 14 2011):
n*a(n) + 2*(8-7*n)*a(n-1) + 45*(n-2)*a(n-2) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-5*x) = 1-9*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1-5*x) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*G = 3 - T;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (2)*(6) + (-12)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a154623

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A154623, for n ≥ 2. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - 5 * X) = 1 - 9 * X →
    coeff 0 T = 1 →
    2 * G = 3 - T →
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℚ)) * coeff n G + (16 - 14 * (n : ℚ)) * coeff (n - 1) G +
        (-90 + 45 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a154623
