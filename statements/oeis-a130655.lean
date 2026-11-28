import Mathlib

/-!
# A130655: Mathar's recurrence

Source: https://oeis.org/A130655
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A130655 (offset 0): catalan transform of Catalan numbers C(n+1);
data 1, 2, 7, 28, 119, 524, 2363, 10844, 50446, 237280, 1126437, 5389916, ...

Conjecture (R. J. Mathar, Mar 01 2015):
3*n*(n-2)*(n+2)*a(n) +4*(-10*n^3+21*n^2+7*n-15)*a(n-1) +16*(11*n^3-47*n^2+57*n-15)*a(n-2)
-8*(2*n-5)*(4*n-9)*(4*n-7)*a(n-3) = 0.

Formalization: The entry gives the g.f. (C(x*C(x))-1)/(x*C(x)), with C(x) the Catalan g.f. (Vladimir Kruchinin, Jul 02
2015), and this is used as the definition here. T is the formal power series over ℚ with T^2 = 1-4*x
and constant term 1; U is the Catalan g.f. C(x), determined by 2*x*U = 1 - T; V is the formal power
series with V^2 = 1 - 4*x*U and constant term 1, that is V = sqrt(1 - 4*x*C(x)) (the constant terms
select the branches of the square roots), so that C(x*C(x)) = (1 - V)/(2*x*U); and G is determined by
G*(2*x^2*U^2) = 1 - V - 2*x*U, the stated expression multiplied by 2*x^2*C(x)^2 (its constant term 1 is
recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (45)*(28) + (-300)*(7) + (480)*(2) + (-120)*(1) = 0.
-/

namespace OMA.S_oeis_a130655

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A130655, for n ≥ 3. -/
theorem main : ∀ T U V G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    2 * X * U = 1 - T →
    V ^ 2 = 1 - 4 * X * U →
    coeff 0 V = 1 →
    G * (2 * X ^ 2 * U ^ 2) = 1 - V - 2 * X * U →
    coeff 0 G = 1 →
    ∀ n : ℕ, 3 ≤ n →
      (-12 * (n : ℚ) + 3 * (n : ℚ) ^ 3) * coeff n G + (-60 + 28 * (n : ℚ) + 84 * (n : ℚ) ^ 2 - 40 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-240 + 912 * (n : ℚ) - 752 * (n : ℚ) ^ 2 + 176 * (n : ℚ) ^ 3) * coeff (n - 2) G + (2520 - 3568 * (n : ℚ) + 1664 * (n : ℚ) ^ 2 - 256 * (n : ℚ) ^ 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a130655
