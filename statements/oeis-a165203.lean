import Mathlib

/-!
# A165203: Mathar's recurrence

Source: https://oeis.org/A165203
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A165203 (offset 0): expansion of (1+x)*c(x)^3/(1-x*c(x)^3), c(x) the g.f. of A000108;
data 1, 5, 20, 81, 332, 1372, 5702, 23793, 99576, 417664, 1754866, 7383204, ...

Conjecture (R. J. Mathar, Dec 11 2011):
(n+1)*(5*n-31)*a(n) +(5*n^2+74*n+62)*a(n-1) +(-285*n^2+ 1072*n-757)*a(n-2)
+(695*n^2-3674*n+4206)*a(n-3) +2*(45*n-74)*(2*n-7)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - x*c^3) = (1+x)*c^3;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-55)*(332) + (438)*(81) + (-1029)*(20) + (630)*(5) + (212)*(1) = 0.
-/

namespace OMA.S_oeis_a165203

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A165203, for n ≥ 4. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - X * c ^ 3) = (1 + X) * c ^ 3 →
    ∀ n : ℕ, 4 ≤ n →
      (-31 - 26 * (n : ℚ) + 5 * (n : ℚ) ^ 2) * coeff n G + (62 + 74 * (n : ℚ) + 5 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-757 + 1072 * (n : ℚ) - 285 * (n : ℚ) ^ 2) * coeff (n - 2) G + (4206 - 3674 * (n : ℚ) + 695 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (1036 - 926 * (n : ℚ) + 180 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a165203
