import Mathlib

/-!
# A172064: Mathar's recurrence

Source: https://oeis.org/A172064
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172064 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=7;
data 1, 8, 46, 230, 1068, 4744, 20476, 86662, 361711, 1494384, 6126818, 24972326, ...

Conjecture (R. J. Mathar, Feb 19 2016):
2*n*(n+7)*(3*n+11)*a(n) -(21*n^3+212*n^2+719*n+840)*a(n-1) -2*(2*n+5)*(n+3)*(3*n+14)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^7;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (612)*(46) + (-3294)*(8) + (-1800)*(1) = 0.
-/

namespace OMA.S_oeis_a172064

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172064, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 7 →
    ∀ n : ℕ, 2 ≤ n →
      (154 * (n : ℚ) + 64 * (n : ℚ) ^ 2 + 6 * (n : ℚ) ^ 3) * coeff n G + (-840 - 719 * (n : ℚ) - 212 * (n : ℚ) ^ 2 - 21 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-420 - 398 * (n : ℚ) - 122 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172064
