import Mathlib

/-!
# A097189: Mathar's recurrence

Source: https://oeis.org/A097189
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A097189 (offset 0): row sums of triangle A097186, in which the n-th row polynomial R_n(y) is formed from the initial (n+1) terms of g.f. A057083(y)^(n+1), where R_n(1/3) = 3^n for all n >= 0;
data 1, 7, 55, 451, 3781, 32131, 275563, 2378971, 20640907, 179791327, 1571002291, 13762897435, ...

Conjecture (R. J. Mathar, Nov 16 2012):
n*(n-1)*a(n) - (19*n-18)*(n-1)*a(n-1) + 9*(11*n^2-31*n+22)*a(n-2) - 9*(3*n-4)*(3*n-5)*a(n-3) = 0.

Formalization: The entry gives the g.f. A(x) = 3/((1-9*x) + 2*(1-9*x)^(2/3)), and this closed form is used as the
definition here. T is the formal power series over ℚ with T^3 = 1-9*x and constant term 1, that is
T = (1-9x)^(1/3); and G is determined by G*((1-9*x) + 2*T^2) = 3 (its constant term 1 is recorded as a
hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (6)*(451) + (-78)*(55) + (252)*(7) + (-180)*(1) = 0.
-/

namespace OMA.S_oeis_a097189

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A097189, for n ≥ 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 3 = 1 - 9 * X →
    coeff 0 T = 1 →
    G * ((1 - 9 * X) + 2 * T ^ 2) = 3 →
    coeff 0 G = 1 →
    ∀ n : ℕ, 3 ≤ n →
      (-(n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-18 + 37 * (n : ℚ) - 19 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (198 - 279 * (n : ℚ) + 99 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-180 + 243 * (n : ℚ) - 81 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a097189
