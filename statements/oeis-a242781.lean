import Mathlib

/-!
# A242781: Mathar's recurrence

Source: https://oeis.org/A242781
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A242781 (offset 0): expansion of (1 - 2*x - sqrt(1-4*x))/(4*x^2 + sqrt(1-4*x)*(3*x+1) - 5*x + 1);
data 0, 0, 1, 4, 15, 57, 217, 828, 3169, 12165, 46827, 180701, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
3*(n+1)*a(n) - 18*n*a(n-1) + 2*(11*n-13)*a(n-2) + 6*(n-7)*a(n-3) + (7*n-9)*a(n-4)
+ 2*(2*n-7)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(4*x^2 + S*(3*x+1) - 5*x + 1) = 1 - 2*x - S (the factor on the left has constant term 2);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (18)*(57) + (-90)*(15) + (84)*(4) + (-12)*(1) + (26)*(0) + (6)*(0) = 0.
-/

namespace OMA.S_oeis_a242781

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A242781, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * (4 * X ^ 2 + S * (3 * X + 1) - 5 * X + 1) = 1 - 2 * X - S →
    ∀ n : ℕ, 5 ≤ n →
      (3 + 3 * (n : ℚ)) * coeff n G + (-18 * (n : ℚ)) * coeff (n - 1) G +
        (-26 + 22 * (n : ℚ)) * coeff (n - 2) G + (-42 + 6 * (n : ℚ)) * coeff (n - 3) G +
        (-9 + 7 * (n : ℚ)) * coeff (n - 4) G + (-14 + 4 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a242781
