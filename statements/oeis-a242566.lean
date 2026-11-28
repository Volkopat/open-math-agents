import Mathlib

/-!
# A242566: Mathar's recurrence

Source: https://oeis.org/A242566
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation -18*x + 6 + (36*x -
12)*y(x) + (1088*x^4 - 396*x^3 - 96*x^2 + 50*x - 6)*y'(x) + (544*x^5 - 196*x^4 - 120*x^3 + 49*x^2
- 4*x)*y''(x) satisfied by the G.f. - Robert Israel, Oct 06 2026

A242566 (offset 0): expansion of (1-sqrt(1-(2*(1-sqrt(1-4*x^2)))/x))/2;
data 0, 1, 1, 3, 7, 22, 67, 225, 765, 2704, 9710, 35558, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
2*n*(2*n+1)*a(n) +(-49*n^2+97*n-36)*a(n-1) +12*(10*n^2-42*n+41)*a(n-2) +4*(49*n-97)*(n-3)*a(n-3)
-544*(n-3)*(n-4)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x^2 and constant term 1; U is the formal power
series with x*U^2 = x - 2*(1-T) and constant term 1, that is U = sqrt(1 - 2*(1 - sqrt(1-4x^2))/x) (the
constant terms select the branches of the square roots); and G is given by 2*G = 1 - U (its constant
term 0 follows from that of U and is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (72)*(7) + (-432)*(3) + (396)*(1) + (396)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a242566

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A242566, for n ≥ 4. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 T = 1 →
    X * U ^ 2 = X - 2 * (1 - T) →
    coeff 0 U = 1 →
    2 * G = 1 - U →
    coeff 0 G = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (2 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (-36 + 97 * (n : ℚ) - 49 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (492 - 504 * (n : ℚ) + 120 * (n : ℚ) ^ 2) * coeff (n - 2) G + (1164 - 976 * (n : ℚ) + 196 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-6528 + 3808 * (n : ℚ) - 544 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a242566
