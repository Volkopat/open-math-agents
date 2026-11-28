import Mathlib

/-!
# A045743: Mathar's recurrence

Source: https://oeis.org/A045743
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A045743 (offset 2): number of noncrossing connected graphs on n nodes on a circle having no triangular
faces;
data 1, 3, 13, 66, 367, 2164, 13293, 84157, 545270, 3598244, 24100375, 163416748, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
5*n*(n-1)*(n-2)*(1353818*n-3651663)*a(n) +16*(n-1)*(n-2)*(2236406*n^2-6864025*n+2014500)*a(n-1)
-16*(n-2)*(46338048*n^3-326486432*n^2+734160494*n-506411475)*a(n-2)
+8*(2*n-7)*(26592864*n^3-436441232*n^2+2071128458*n-3030735075)*a(n-3)
+128*(94246*n-334675)*(4*n-19)*(2*n-9)*(4*n-17)*a(n-4) = 0.

Formalization: the entry gives (Paul D. Hanna, Mar 09 2010): with A(x) the g.f. and
F(x) = 1 + A(x)/x = 1 + x + 3*x^2 + 13*x^3 + 66*x^4 + ..., F satisfies
x*F(x)^4 = (1 - F(x))*(1 - 3*F(x) + F(x)^2); this is used as the definition here. F is the formal power
series over ℚ with constant term 1 satisfying this equation (at x = 0 the equation reads
(1-F)*(1-3F+F^2) = 0, and the constant term 1 selects the series among the solutions), and
a(n) = [x^(n-1)] F for n ≥ 2. The sequence has offset 2 and the recurrence involves a(n-4), so it is
stated for n ≥ 6, where every index is at least the offset; it is checked by the data, for example at
n = 6: (5*6*5*4*4471245)*(367) + (16*5*4*41340966)*(66) - (16*4*2154058305)*(13)
+ (8*5*(-571790055))*(3) + (128*230801*5*3*7)*(1) = 0.
-/

namespace OMA.S_oeis_a045743

open PowerSeries

/-- Mathar's conjectured recurrence for A045743 (a(n) = [x^(n-1)] F), for n ≥ 6. -/
theorem main : ∀ F : ℚ⟦X⟧, coeff 0 F = 1 →
    X * F ^ 4 = (1 - F) * (1 - 3 * F + F ^ 2) →
    ∀ n : ℕ, 6 ≤ n →
      5 * (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * (1353818 * (n : ℚ) - 3651663) * coeff (n - 1) F +
        16 * ((n : ℚ) - 1) * ((n : ℚ) - 2) *
          (2236406 * (n : ℚ) ^ 2 - 6864025 * (n : ℚ) + 2014500) * coeff (n - 2) F -
        16 * ((n : ℚ) - 2) * (46338048 * (n : ℚ) ^ 3 - 326486432 * (n : ℚ) ^ 2 +
          734160494 * (n : ℚ) - 506411475) * coeff (n - 3) F +
        8 * (2 * (n : ℚ) - 7) * (26592864 * (n : ℚ) ^ 3 - 436441232 * (n : ℚ) ^ 2 +
          2071128458 * (n : ℚ) - 3030735075) * coeff (n - 4) F +
        128 * (94246 * (n : ℚ) - 334675) * (4 * (n : ℚ) - 19) * (2 * (n : ℚ) - 9) *
          (4 * (n : ℚ) - 17) * coeff (n - 5) F = 0 := by
  sorry

end OMA.S_oeis_a045743
