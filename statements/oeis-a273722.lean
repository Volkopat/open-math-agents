import Mathlib

/-!
# A273722: Mathar's recurrence

Source: https://oeis.org/A273722
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jun 02 2016); the entry records it as a conjecture and notes no proof or
verification of it.

A273722 (offset 2): the number of valleys of width 1 (i.e., DHU configurations, where U=(0,1), H(1,0),
D=(0,-1)) in all bargraphs of semiperimeter n (n>=2);
data 0, 0, 0, 0, 1, 7, 34, 143, 558, 2083, 7559, 26913, ...

Conjecture (R. J. Mathar, Jun 02 2016):
-(n-6) *(2*n-7) *(2*n-9) *(n+1)*a(n) +2*(n-3) *(2*n-9) *(4*n^2-24*n+21)*a(n-1)
+2*(-4*n^4+56*n^3-289*n^2+651*n-547) *a(n-2) +4*(2*n-5) *(n-4)*a(n-3)
-(n-4) *(n-5) *(2*n-5) *(2*n-7) *a(n-4) = 0.

Formalization: the entry gives the g.f. g(z) = (1-5z+6z^2-z^3+z^4-(1-3z+z^2)Q)/(2zQ) with
Q = sqrt(1-4z+2z^2+z^4), and this closed form is used as the definition here. T is the formal power series
over ℚ with T^2 = 1-4*x+2*x^2+x^4 and constant term 1, that is T = Q (the constant term selects the branch of
the square root); and G is determined by G*2*x*T = 1-5*x+6*x^2-x^3+x^4 - (1-3*x+x^2)*T, the stated expression
multiplied by its denominator (the denominator is a nonzero power series, so this equation has exactly one
solution G); a(n) = [x^n] G. The sequence has offset 2 and the recurrence involves a(n-4), so it is stated
for n ≥ 6, where every index is at least the offset; it is checked by the data, for example at n = 7:
(-280)*(7) + (1960)*(1) + (-1094)*(0) + (108)*(0) + (-378)*(0) = 0, and at n = 8:
(-1134)*(34) + (5950)*(7) + (-3094)*(1) + (176)*(0) + (-1188)*(0) = 0.
-/

namespace OMA.S_oeis_a273722

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A273722, for n ≥ 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4 →
    coeff 0 T = 1 →
    G * (2 * X * T) = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4 - (1 - 3 * X + X ^ 2) * T →
    ∀ n : ℕ, 6 ≤ n →
      (378 + 123 * (n : ℚ) - 199 * (n : ℚ) ^ 2 + 52 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4) * coeff n G + (1134 - 1926 * (n : ℚ) + 1020 * (n : ℚ) ^ 2 - 216 * (n : ℚ) ^ 3 + 16 * (n : ℚ) ^ 4) * coeff (n - 1) G +
        (-1094 + 1302 * (n : ℚ) - 578 * (n : ℚ) ^ 2 + 112 * (n : ℚ) ^ 3 - 8 * (n : ℚ) ^ 4) * coeff (n - 2) G + (80 - 52 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-700 + 795 * (n : ℚ) - 331 * (n : ℚ) ^ 2 + 60 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a273722
