import Mathlib

/-!
# A114194: Mathar's recurrence

Source: https://oeis.org/A114194
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A114194 (offset 0): expansion of 1/(1+x*(2-x)*c(-2*x)), c(x) the g.f. of A000108;
data 1, -2, 9, -46, 261, -1578, 9969, -65030, 434685, -2961922, 20497577, -143673630, ...

Conjecture (R. J. Mathar, Dec 10 2011):
6*(n+1)*a(n) + (37n-29)*a(n-1) + 2*(45-41n)*a(n-2) + (47n-87)*a(n-3) + 4*(5-2n)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1+8*x and constant term 1, that is S = sqrt(1+8x)
(the constant term selects the branch of the square root); c is the series c(-2x), with c(x) the Catalan
g.f., determined by -4*x*c = 1 - S; and the g.f. G is determined by G*(1 + x*(2-x)*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (30)*(261) + (119)*(-46) + (-238)*(9) + (101)*(-2) + (-12)*(1) = 0.
-/

namespace OMA.S_oeis_a114194

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A114194, for n ≥ 4. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 + 8 * X →
    coeff 0 S = 1 →
    -(4 * X * c) = 1 - S →
    G * (1 + X * (2 - X) * c) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (6 + 6 * (n : ℚ)) * coeff n G + (-29 + 37 * (n : ℚ)) * coeff (n - 1) G +
        (90 - 82 * (n : ℚ)) * coeff (n - 2) G + (-87 + 47 * (n : ℚ)) * coeff (n - 3) G +
        (20 - 8 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a114194
