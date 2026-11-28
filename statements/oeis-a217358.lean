import Mathlib

/-!
# A217358: Mathar's recurrence

Source: https://oeis.org/A217358
Credit: @ivillar

Status: open conjecture (R. J. Mathar); the entry records it as a conjecture and notes no proof or
verification of it.

A217358 (offset 1): series reversion of x-x^3-x^4;
data 1, 0, 1, 1, 3, 7, 16, 45, 110, 308, 819, 2275, ...

Conjecture (R. J. Mathar):
46*n*(n-1)*(n-2)*a(n) -(n-1)*(n-2)*(11*n-74)*a(n-1) -(n-2)*(336*n^2-1359*n+1351)*a(n-2)
+(-347*n^3+2190*n^2-3861*n+1330)*a(n-3) + 8*(2*n-7)*(4*n-15)*(4*n-17)*a(n-4) = 0.

Formalization: The sequence is the series reversion of x - x^3 - x^4. G is the formal power series over ℚ with zero
constant term and G - G^3 - G^4 = x, that is the compositional inverse of x - x^3 - x^4 (this equation
has exactly one power series solution with zero constant term);
a(n) = [x^n] G. The sequence has offset 1 and the recurrence involves a(n-4), so it is stated for n ≥ 5,
where every index is at least the offset; it is checked by the data, for example at n = 5:
(2760)*(3) + (228)*(1) + (-8868)*(1) + (-6600)*(0) + (360)*(1) = 0.
-/

namespace OMA.S_oeis_a217358

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A217358, for n ≥ 5. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    G - G ^ 3 - G ^ 4 = X →
    ∀ n : ℕ, 5 ≤ n →
      (92 * (n : ℚ) - 138 * (n : ℚ) ^ 2 + 46 * (n : ℚ) ^ 3) * coeff n G + (148 - 244 * (n : ℚ) + 107 * (n : ℚ) ^ 2 - 11 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (2702 - 4069 * (n : ℚ) + 2031 * (n : ℚ) ^ 2 - 336 * (n : ℚ) ^ 3) * coeff (n - 2) G + (1330 - 3861 * (n : ℚ) + 2190 * (n : ℚ) ^ 2 - 347 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-14280 + 11248 * (n : ℚ) - 2944 * (n : ℚ) ^ 2 + 256 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a217358
