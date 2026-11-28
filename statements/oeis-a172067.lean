import Mathlib

/-!
# A172067: Mathar's recurrence

Source: https://oeis.org/A172067
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172067 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=10;
data 1, 11, 79, 468, 2486, 12323, 58277, 266492, 1188679, 5202523, 22436251, 95630272, ...

Conjecture (R. J. Mathar, Feb 21 2016):
2*n*(n+10)*(3*n+17)*a(n) - (21*n^3 + 317*n^2 + 1622*n + 2880)*a(n-1) -
2*(3*n+20)*(n+4)*(2*n+9)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^10;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (1104)*(79) + (-7560)*(11) + (-4056)*(1) = 0.
-/

namespace OMA.S_oeis_a172067

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172067, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 10 →
    ∀ n : ℕ, 2 ≤ n →
      (340 * (n : ℚ) + 94 * (n : ℚ) ^ 2 + 6 * (n : ℚ) ^ 3) * coeff n G + (-2880 - 1622 * (n : ℚ) - 317 * (n : ℚ) ^ 2 - 21 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-1440 - 896 * (n : ℚ) - 182 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172067
