import Mathlib

/-!
# A276314: Mathar's recurrence

Source: https://oeis.org/A276314
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A276314 (offset 1): g.f. A(x) satisfies: x = A(x)-A(x)^2-3*A(x)^3;
data 1, 1, 5, 20, 104, 546, 3066, 17655, 104555, 630773, 3867617, 24020932, ...

Conjecture (R. J. Mathar, Sep 17 2016):
+169*n*(n+2)*(n-1)*a(n) +13*(n-1) *(13*n^2+26*n-220) *a(n-1)
+(-7277*n^3+13423*n^2+43814*n-81700) *a(n-2) -27*(3*n-10) *(3*n-8) *(71*n+197)*a(n-3) = 0.

Formalization: G is the formal power series over ℚ with zero constant term and x = G - G^2 - 3*G^3 (the series
reversion of x - x^2 - 3*x^3);
a(n) = [x^n] G. The sequence has offset 1 and the recurrence involves a(n-3), so it is stated for n ≥ 4,
where every index is at least the offset; it is checked by the data, for example at n = 4:
(12168)*(20) + (3588)*(5) + (-157404)*(1) + (-103896)*(1) = 0.
-/

namespace OMA.S_oeis_a276314

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A276314, for n ≥ 4. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    X = G - G ^ 2 - 3 * G ^ 3 →
    ∀ n : ℕ, 4 ≤ n →
      (-338 * (n : ℚ) + 169 * (n : ℚ) ^ 2 + 169 * (n : ℚ) ^ 3) * coeff n G + (2860 - 3198 * (n : ℚ) + 169 * (n : ℚ) ^ 2 + 169 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-81700 + 43814 * (n : ℚ) + 13423 * (n : ℚ) ^ 2 - 7277 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-425520 + 133866 * (n : ℚ) + 55647 * (n : ℚ) ^ 2 - 17253 * (n : ℚ) ^ 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a276314
