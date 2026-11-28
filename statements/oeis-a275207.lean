import Mathlib

/-!
# A275207: Mathar's recurrence

Source: https://oeis.org/A275207
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A275207 (offset 0): expansion of (A(x)^2+A(x^2))/2 where A(x) = A001006(x);
data 1, 1, 3, 6, 16, 38, 100, 256, 681, 1805, 4867, 13162, ...

Conjecture (R. J. Mathar, Mar 07 2023): D-finite with recurrence
-3*(n+4)*(n+3)*(29*n-32)*a(n) +10*(29*n-40)*(n+3)*(n+2)*a(n-1) +2*(n+1)*(149*n^2
+208*n-450)*a(n-2) -2*n*(559*n^2 -381*n-1630)*a(n-3) +4*(-68*n^3 +531*n^2 -904*n+351)*a(n-4)
+2*(103*n^3-1701*n^2+5330*n -3600)*a(n-5) +18*(11*n^3 -209*n^2 +834*n -778)*a(n-6)
+6*n*(269*n-830)*(n-5)*a(n-7) +9*(n-5)*(n-6)*(95*n-134)*a(n-8) = 0.

Formalization: T and W are the formal power series over ℚ with T^2 = 1-2*x-3*x^2, W^2 = 1-2*x^2-3*x^4 and constant
terms 1 (the constant terms select the branches of the square roots), so that the Motzkin g.f. is
A(x) = (1-x-T)/(2*x^2) and A(x^2) = (1-x^2-W)/(2*x^4); the g.f. G = (A(x)^2 + A(x^2))/2 is determined by
8*x^4*G = (1-x-T)^2 + 2*(1-x^2-W) (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-8), so it is stated for n ≥ 8; it is checked by the data, for
example at n = 8: (-79200)*(681) + (211200)*(256) + (193500)*(100) + (-497568)*(38) + (-30852)*(16) + (-34176)*(6) + (-33300)*(3) + (190368)*(1) + (33804)*(1) = 0.
-/

namespace OMA.S_oeis_a275207

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A275207, for n ≥ 8. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 T = 1 →
    W ^ 2 = 1 - 2 * X ^ 2 - 3 * X ^ 4 →
    coeff 0 W = 1 →
    8 * X ^ 4 * G = (1 - X - T) ^ 2 + 2 * (1 - X ^ 2 - W) →
    coeff 0 G = 1 →
    ∀ n : ℕ, 8 ≤ n →
      (1152 - 372 * (n : ℚ) - 513 * (n : ℚ) ^ 2 - 87 * (n : ℚ) ^ 3) * coeff n G + (-2400 - 260 * (n : ℚ) + 1050 * (n : ℚ) ^ 2 + 290 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-900 - 484 * (n : ℚ) + 714 * (n : ℚ) ^ 2 + 298 * (n : ℚ) ^ 3) * coeff (n - 2) G + (3260 * (n : ℚ) + 762 * (n : ℚ) ^ 2 - 1118 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (1404 - 3616 * (n : ℚ) + 2124 * (n : ℚ) ^ 2 - 272 * (n : ℚ) ^ 3) * coeff (n - 4) G + (-7200 + 10660 * (n : ℚ) - 3402 * (n : ℚ) ^ 2 + 206 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (-14004 + 15012 * (n : ℚ) - 3762 * (n : ℚ) ^ 2 + 198 * (n : ℚ) ^ 3) * coeff (n - 6) G + (24900 * (n : ℚ) - 13050 * (n : ℚ) ^ 2 + 1614 * (n : ℚ) ^ 3) * coeff (n - 7) G +
        (-36180 + 38916 * (n : ℚ) - 10611 * (n : ℚ) ^ 2 + 855 * (n : ℚ) ^ 3) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a275207
