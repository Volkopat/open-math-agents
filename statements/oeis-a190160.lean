import Mathlib

/-!
# A190160: Mathar's recurrence

Source: https://oeis.org/A190160
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A190160 (offset 0): number of peakless Motzkin paths of length n containing no subwords of  type uh^ju or dh^jd (j>=1), where u=(1,1), h=(1,0), and d=(1,-1) (can be easily expressed using RNA secondary structure terminology);
data 1, 1, 1, 2, 4, 8, 15, 28, 53, 102, 199, 391, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+2)*a(n) +(-5*n-6)*a(n-1) +2*(4*n+3)*a(n-2) +(-2*n-9)*a(n-3) +(-8*n+25)*a(n-4) +6*(n-2)*a(n-5)
+9*(n-7)*a(n-6) +3*(-5*n+32)*a(n-7) +7*(n-7)*a(n-8) +(-n+8)*a(n-9) = 0.

Formalization: The entry gives the equation G = 1 + z*G + z^2*G*[z + (1-z)^2*(G - z*G - 1)]/(1-z) for the g.f.; multiplied by
1 - x it reads (1-x)*G = (1-x) + x*(1-x)*G + x^2*G*(x + (1-x)^2*(G - x*G - 1)), and G is the formal power
series over ℚ satisfying this (it has exactly one power series solution, with constant term 1);
a(n) = [x^n] G. The recurrence involves a(n-9), so it is stated for n ≥ 9; it is checked by the data, for
example at n = 9: (11)*(102) + (-51)*(53) + (78)*(28) + (-27)*(15) + (-47)*(8) + (42)*(4) + (18)*(2) + (-39)*(1) + (14)*(1) + (-1)*(1) = 0.
-/

namespace OMA.S_oeis_a190160

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A190160, for n ≥ 9. -/
theorem main : ∀ G : ℚ⟦X⟧, (1 - X) * G = (1 - X) + X * (1 - X) * G + X ^ 2 * G * (X + (1 - X) ^ 2 * (G - X * G - 1)) →
    ∀ n : ℕ, 9 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-6 - 5 * (n : ℚ)) * coeff (n - 1) G +
        (6 + 8 * (n : ℚ)) * coeff (n - 2) G + (-9 - 2 * (n : ℚ)) * coeff (n - 3) G +
        (25 - 8 * (n : ℚ)) * coeff (n - 4) G + (-12 + 6 * (n : ℚ)) * coeff (n - 5) G +
        (-63 + 9 * (n : ℚ)) * coeff (n - 6) G + (96 - 15 * (n : ℚ)) * coeff (n - 7) G +
        (-49 + 7 * (n : ℚ)) * coeff (n - 8) G + (8 - (n : ℚ)) * coeff (n - 9) G = 0 := by
  sorry

end OMA.S_oeis_a190160
