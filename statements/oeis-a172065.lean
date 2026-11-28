import Mathlib

/-!
# A172065: Mathar's recurrence

Source: https://oeis.org/A172065
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172065 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=8;
data 1, 9, 56, 297, 1444, 6656, 29618, 128603, 548591, 2309467, 9624964, 39799813, ...

Conjecture (R. J. Mathar, Feb 29 2016):
2*n*(n+8)*(3*n+13)*a(n) -(21*n^3 + 247*n^2 + 980*n + 1344)*a(n-1) -
2*(n+3)*(3*n+16)*(2*n+7)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^8;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (760)*(56) + (-4460)*(9) + (-2420)*(1) = 0.
-/

namespace OMA.S_oeis_a172065

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172065, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 8 →
    ∀ n : ℕ, 2 ≤ n →
      (208 * (n : ℚ) + 74 * (n : ℚ) ^ 2 + 6 * (n : ℚ) ^ 3) * coeff n G + (-1344 - 980 * (n : ℚ) - 247 * (n : ℚ) ^ 2 - 21 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-672 - 542 * (n : ℚ) - 142 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172065
