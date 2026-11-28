import Mathlib

/-!
# A006605: Mathar's recurrence

Source: https://oeis.org/A006605
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A006605 (offset 0): number of modes of connections of 2n points;
data 1, 1, 3, 11, 46, 207, 979, 4797, 24138, 123998, 647615, 3428493, ...

Conjecture (R. J. Mathar, May 30 2014):
3*n*(3*n+2)*(3*n+1)*a(n) + (-275*n^3 + 475*n^2 - 328*n + 68)*a(n-1) + 2*(2*n-3)*(139*n^2 - 507*n +
398)*a(n-2) + 180*(2*n-5)*(n-2)*(2*n-3)*a(n-3) = 0.

Formalization: The entry gives the g.f. as A(x) = (1/x)*serreverse(x/M(x)) with M the g.f. of the Motzkin numbers
(Paul D. Hanna, Mar 20 2005). Since M(y) = 1 + y*M(y) + y^2*M(y)^2, putting y = x*A(x), for which
M(y) = y/x = A(x), gives A = 1 + x*A^2 + x^2*A^4; equivalently x*A^2 is the reversion of
x/(1+x+x^2)^2, as stated in the entry. G is the formal power series over ℚ with
G = 1 + x*G^2 + x^2*G^4 (this equation has exactly one power series solution, with constant term 1);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (990)*(11) + (-4066)*(3) + (768)*(1) + (540)*(1) = 0.
-/

namespace OMA.S_oeis_a006605

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A006605, for n ≥ 3. -/
theorem main : ∀ G : ℚ⟦X⟧, G = 1 + X * G ^ 2 + X ^ 2 * G ^ 4 →
    ∀ n : ℕ, 3 ≤ n →
      (6 * (n : ℚ) + 27 * (n : ℚ) ^ 2 + 27 * (n : ℚ) ^ 3) * coeff n G + (68 - 328 * (n : ℚ) + 475 * (n : ℚ) ^ 2 - 275 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-2388 + 4634 * (n : ℚ) - 2862 * (n : ℚ) ^ 2 + 556 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-5400 + 8460 * (n : ℚ) - 4320 * (n : ℚ) ^ 2 + 720 * (n : ℚ) ^ 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a006605
