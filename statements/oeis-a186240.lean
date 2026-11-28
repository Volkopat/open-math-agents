import Mathlib

/-!
# A186240: Mathar's recurrence

Source: https://oeis.org/A186240
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A186240 (offset 0): g.f. A(x) defined by A(x) = 1 +x*A(x) +x^2*A(x)^2 +3*x^3*A(x)^3;
data 1, 1, 2, 7, 21, 66, 228, 799, 2843, 10357, 38278, 143012, ...

Conjecture (R. J. Mathar, Sep 27 2013):
6*(2*n+3)*(n+1)*a(n) +(277*n^2-191*n-162)*a(n-1) +6*(-155*n^2+305*n-126)*a(n-2)
-4*(181*n-195)*(n-2)*a(n-3) -5304*(n-2)*(n-3)*a(n-4) = 0.

Formalization: G is the formal power series over ℚ with G = 1 + x*G + x^2*G^2 + 3*x^3*G^3; this equation
determines G, and its constant term is 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (330)*(21) + (3506)*(7) + (-8316)*(2) + (-4232)*(1) + (-10608)*(1) = 0.
-/

namespace OMA.S_oeis_a186240

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A186240, for n ≥ 4. -/
theorem main : ∀ G : ℚ⟦X⟧, G = 1 + X * G + X ^ 2 * G ^ 2 + 3 * X ^ 3 * G ^ 3 →
    ∀ n : ℕ, 4 ≤ n →
      (18 + 30 * (n : ℚ) + 12 * (n : ℚ) ^ 2) * coeff n G + (-162 - 191 * (n : ℚ) + 277 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-756 + 1830 * (n : ℚ) - 930 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-1560 + 2228 * (n : ℚ) - 724 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-31824 + 26520 * (n : ℚ) - 5304 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a186240
