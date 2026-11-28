import Mathlib

/-!
# A190163: Mathar's recurrence

Source: https://oeis.org/A190163
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A190163 (offset 0): number of subwords of type dh^ju (j>=1), where u=(1,1), h=(1,0), and d=(1,-1), in all peakless Motzkin paths of length n (can be easily expressed using RNA secondary structure terminology);
data 0, 0, 0, 0, 0, 0, 0, 1, 5, 18, 58, 174, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
-4*(n+1)*(n-7)*a(n) +(13*n^2-85*n+28)*a(n-1) +(-7*n^2+52*n-41)*a(n-2) +(5*n^2-41*n+67)*a(n-3)
+(-13*n^2+103*n-197)*a(n-4) +(7*n-29)*(n-5)*a(n-5) -(n-5)*(n-6)*a(n-6) = 0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T*(T-1) (this
equation has exactly one power series solution, with constant term 1; it is the g.f. of the peakless
Motzkin paths); and the g.f. G is determined by
G*(1 - x)*(1 - x^2*T^2) = x^5*T^2*(T-1)^2, the stated expression multiplied by its denominator;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (28)*(0) + (-14)*(0) + (19)*(0) + (1)*(0) + (-47)*(0) + (13)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a190163

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A190163, for n ≥ 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T * (T - 1) →
    G * ((1 - X) * (1 - X ^ 2 * T ^ 2)) = X ^ 5 * T ^ 2 * (T - 1) ^ 2 →
    ∀ n : ℕ, 6 ≤ n →
      (28 + 24 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff n G + (28 - 85 * (n : ℚ) + 13 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-41 + 52 * (n : ℚ) - 7 * (n : ℚ) ^ 2) * coeff (n - 2) G + (67 - 41 * (n : ℚ) + 5 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-197 + 103 * (n : ℚ) - 13 * (n : ℚ) ^ 2) * coeff (n - 4) G + (145 - 64 * (n : ℚ) + 7 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (-30 + 11 * (n : ℚ) - (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a190163
