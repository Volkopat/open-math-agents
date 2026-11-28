import Mathlib

/-!
# A158197: Mathar's recurrence

Source: https://oeis.org/A158197
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A158197 (offset 0): expansion of (1-x^2*c(x)^4)/(1-4*x*c(x)^2), c(x) the g.f. of A000108;
data 1, 4, 23, 140, 866, 5388, 33603, 209796, 1310510, 8188328, 51169094, 319779544, ...

Conjecture (R. J. Mathar, Feb 05 2015):
+4*(n+1)*a(n) +(-81*n+23)*a(n-1) +10*(51*n-70)*a(n-2) +500*(-2*n+5)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - 4*x*c^2) = 1 - x^2*c^4;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (16)*(140) + (-220)*(23) + (830)*(4) + (-500)*(1) = 0.
-/

namespace OMA.S_oeis_a158197

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A158197, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - 4 * X * c ^ 2) = 1 - X ^ 2 * c ^ 4 →
    ∀ n : ℕ, 3 ≤ n →
      (4 + 4 * (n : ℚ)) * coeff n G + (23 - 81 * (n : ℚ)) * coeff (n - 1) G +
        (-700 + 510 * (n : ℚ)) * coeff (n - 2) G + (2500 - 1000 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a158197
