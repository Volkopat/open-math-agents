import Mathlib

/-!
# A159772: Mathar's recurrence

Source: https://oeis.org/A159772
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A159772 (offset 1): number of n-leaf binary trees that do not contain (()((((()())())())())) as a subtree;
data 1, 1, 2, 5, 14, 41, 124, 384, 1210, 3865, 12482, 40677, ...

Conjecture (R. J. Mathar, May 30 2014):
2*(n-1)*(2*n-3)*a(n) +(-43*n^2+172*n-177)*a(n-1) +4*(44*n^2-266*n+411)*a(n-2)
+8*(-43*n^2+358*n-741)*a(n-3) +96*(3*n^2-29*n+69)*a(n-4) -128*(n-4)*(n-6)*a(n-5)
+512*(n-6)*(n-7)*a(n-6) = 0.

Formalization: The entry gives the g.f. as x/(1-x*G(x)), where G(x) is the g.f. of A036765 (Andrew Howroyd,
Dec 04 2017), and A036765 records that its g.f. A satisfies A = 1 + z*A + (z*A)^2 + (z*A)^3 (Emeric
Deutsch, Nov 29 2003); this is used as the definition here. T (the g.f. of A036765) is the formal
power series over ℚ with T = 1 + x*T + x^2*T^2 + x^3*T^3 (this equation has exactly one power series
solution, with constant term 1); and the g.f. G is determined by G*(1 - x*T) = x;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (90)*(41) + (-693)*(14) + (1596)*(5) + (-1128)*(2) + (288)*(1) + (0)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a159772

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A159772, for n ≥ 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T ^ 2 + X ^ 3 * T ^ 3 →
    G * (1 - X * T) = X →
    ∀ n : ℕ, 6 ≤ n →
      (6 - 10 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (-177 + 172 * (n : ℚ) - 43 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (1644 - 1064 * (n : ℚ) + 176 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-5928 + 2864 * (n : ℚ) - 344 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (6624 - 2784 * (n : ℚ) + 288 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-3072 + 1280 * (n : ℚ) - 128 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (21504 - 6656 * (n : ℚ) + 512 * (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a159772
