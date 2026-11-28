import Mathlib

/-!
# A186185: Mathar's recurrence

Source: https://oeis.org/A186185
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A186185 (offset 0): expansion of 1/(1 - x*A001764(x/(1-x))/(1-x));
data 1, 1, 3, 11, 48, 239, 1306, 7612, 46436, 292875, 1894365, 12496864, ...

Conjecture (R. J. Mathar, May 07 2024): D-finite with recurrence
2*(2*n-1)*(n-1)*a(n) +(9*n^2-127*n+170)*a(n-1)
+10*(-57*n^2+368*n-559)*a(n-2) +(2579*n^2-18451*n+32892)*a(n-3)
+3*(-1633*n^2+13195*n-26878)*a(n-4) +6*(712*n-3111)*(n-5)*a(n-5) -1395*(n-5)*(n-6)*a(n-6)=0 (stated in the entry for n > 6).

Formalization: T is the series A001764(x/(1-x)), where A001764(y) = 1 + y*A001764(y)^3: it is the formal power series
over ℚ with (1-x)*T = (1-x) + x*T^3 (this equation determines T), and the g.f. G is determined by
G*((1-x) - x*T) = 1 - x, which is the stated expression with numerator and denominator multiplied by
1-x;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (110)*(1306) + (-268)*(239) + (-4030)*(48) + (15030)*(11) + (-19488)*(3) + (6966)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a186185

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A186185, for n ≥ 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, (1 - X) * T = (1 - X) + X * T ^ 3 →
    G * ((1 - X) - X * T) = 1 - X →
    ∀ n : ℕ, 6 ≤ n →
      (2 - 6 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (170 - 127 * (n : ℚ) + 9 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-5590 + 3680 * (n : ℚ) - 570 * (n : ℚ) ^ 2) * coeff (n - 2) G + (32892 - 18451 * (n : ℚ) + 2579 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-80634 + 39585 * (n : ℚ) - 4899 * (n : ℚ) ^ 2) * coeff (n - 4) G + (93330 - 40026 * (n : ℚ) + 4272 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (-41850 + 15345 * (n : ℚ) - 1395 * (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a186185
