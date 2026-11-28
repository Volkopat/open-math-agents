import Mathlib

/-!
# A025757: Mathar's recurrence

Source: https://oeis.org/A025757
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A025757 (offset 0): 4th-order Vatalan numbers (generalization of Catalan numbers);
data 1, 1, 7, 69, 783, 9597, 123495, 1643397, 22413183, 311466829, 4392857431, 62702224213, ...

Conjecture (R. J. Mathar, Jul 28 2014):
5*n*(n-1)*(n-2)*a(n) -(239*n-600)*(n-1)*(n-2)*a(n-1) +24*(n-2)*(158*n^2-953*n+1445)*a(n-2)
+16*(-1232*n^3+13056*n^2-45949*n+53730)*a(n-3) -128*(4*n-15)*(2*n-7)*(4*n-13)*a(n-4) = 0.

Formalization: The entry gives the g.f. 4/(3+(1-16*x)^(1/4)), and this is used as the definition here: T is the formal
power series over ℚ with T^4 = 1-16*x and constant term 1, that is T = (1-16x)^(1/4) (the constant term
selects the branch of the fourth root), and G is determined by G*(3 + T) = 4;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (120)*(783) + (-2136)*(69) + (7728)*(7) + (-288)*(1) + (-384)*(1) = 0.
-/

namespace OMA.S_oeis_a025757

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A025757, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 4 = 1 - 16 * X →
    coeff 0 T = 1 →
    G * (3 + T) = 4 →
    ∀ n : ℕ, 4 ≤ n →
      (10 * (n : ℚ) - 15 * (n : ℚ) ^ 2 + 5 * (n : ℚ) ^ 3) * coeff n G + (1200 - 2278 * (n : ℚ) + 1317 * (n : ℚ) ^ 2 - 239 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-69360 + 80424 * (n : ℚ) - 30456 * (n : ℚ) ^ 2 + 3792 * (n : ℚ) ^ 3) * coeff (n - 2) G + (859680 - 735184 * (n : ℚ) + 208896 * (n : ℚ) ^ 2 - 19712 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (174720 - 150272 * (n : ℚ) + 43008 * (n : ℚ) ^ 2 - 4096 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a025757
