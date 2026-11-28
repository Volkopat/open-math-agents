import Mathlib

/-!
# A172062: Mathar's recurrence

Source: https://oeis.org/A172062
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172062 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=5;
data 1, 6, 29, 128, 541, 2232, 9076, 36568, 146446, 584082, 2322967, 9220544, ...

Conjecture (R. J. Mathar, Feb 19 2016):
2*n*(n+5)*(3*n+7)*a(n) - (n+3)*(21*n^2+79*n+80)*a(n-1) - 2*(3*n+10)*(2*n+3)*(n+2)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^5;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (364)*(29) + (-1610)*(6) + (-896)*(1) = 0.
-/

namespace OMA.S_oeis_a172062

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172062, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 5 →
    ∀ n : ℕ, 2 ≤ n →
      (70 * (n : ℚ) + 44 * (n : ℚ) ^ 2 + 6 * (n : ℚ) ^ 3) * coeff n G + (-240 - 317 * (n : ℚ) - 142 * (n : ℚ) ^ 2 - 21 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-120 - 176 * (n : ℚ) - 82 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172062
