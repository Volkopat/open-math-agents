import Mathlib

/-!
# A097180: Mathar's recurrence

Source: https://oeis.org/A097180
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A097180 (offset 0): row sums of triangle A097179, in which the n-th row polynomial R_n(y) is formed from the initial (n+1) terms of g.f. A077860(y)^(n+1), where R_n(1/2) = 4^n for all n>=0;
data 1, 7, 52, 395, 3036, 23506, 182904, 1428387, 11185900, 87789702, 690212744, 5434455182, ...

Conjecture (R. J. Mathar, Nov 16 2012):
n*(n-1)*(n+1)*a(n) -12*n*(2*n-1)*(n-1)*a(n-1) +12*(n-1) * (16*n^2-32*n+17)*a(n-2)
-16*(4*n-5)*(4*n-7)*(2*n-3)*a(n-3) = 0.

Formalization: The entry gives the g.f. A(x) = 2/((1-8*x) + (1-8*x)^(3/4)), and this closed form is used as the definition
here. T is the formal power series over ℚ with T^4 = 1-8*x and constant term 1, that is T = (1-8x)^(1/4)
(the constant term selects the branch of the root); and G is determined by G*((1-8*x) + T^3) = 2 (its
constant term 1 is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (24)*(395) + (-360)*(52) + (1560)*(7) + (-1680)*(1) = 0.
-/

namespace OMA.S_oeis_a097180

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A097180, for n ≥ 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 4 = 1 - 8 * X →
    coeff 0 T = 1 →
    G * ((1 - 8 * X) + T ^ 3) = 2 →
    coeff 0 G = 1 →
    ∀ n : ℕ, 3 ≤ n →
      (-(n : ℚ) + (n : ℚ) ^ 3) * coeff n G + (-12 * (n : ℚ) + 36 * (n : ℚ) ^ 2 - 24 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-204 + 588 * (n : ℚ) - 576 * (n : ℚ) ^ 2 + 192 * (n : ℚ) ^ 3) * coeff (n - 2) G + (1680 - 3424 * (n : ℚ) + 2304 * (n : ℚ) ^ 2 - 512 * (n : ℚ) ^ 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a097180
