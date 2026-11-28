import Mathlib

/-!
# A158196: Mathar's recurrence

Source: https://oeis.org/A158196
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A158196 (offset 0): expansion of (1-x^2*c(x)^4)/(1-3*x*c(x)^2), c(x) the g.f. of A000108;
data 1, 3, 14, 71, 370, 1950, 10332, 54895, 292106, 1555706, 8289732, 44186710, ...

Conjecture (R. J. Mathar, Feb 05 2015):
+3*(n+1)*a(n) +2*(-26*n+7)*a(n-1) +16*(18*n-25)*a(n-2) +256*(-2*n+5)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - 3*x*c^2) = 1 - x^2*c^4;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (12)*(71) + (-142)*(14) + (464)*(3) + (-256)*(1) = 0.
-/

namespace OMA.S_oeis_a158196

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A158196, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - 3 * X * c ^ 2) = 1 - X ^ 2 * c ^ 4 →
    ∀ n : ℕ, 3 ≤ n →
      (3 + 3 * (n : ℚ)) * coeff n G + (14 - 52 * (n : ℚ)) * coeff (n - 1) G +
        (-400 + 288 * (n : ℚ)) * coeff (n - 2) G + (1280 - 512 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a158196
