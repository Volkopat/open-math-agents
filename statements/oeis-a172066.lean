import Mathlib

/-!
# A172066: Mathar's recurrence

Source: https://oeis.org/A172066
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172066 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=9;
data 1, 10, 67, 376, 1912, 9142, 41941, 186880, 815083, 3498146, 14827487, 62236064, ...

Conjecture (R. J. Mathar, Feb 19 2016):
2*n*(n+9)*(n+5)*a(n) -(7*n^3+94*n^2+427*n+672)*a(n-1) -2*(2*n+7)*(n+6)*(n+4)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^9;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (308)*(67) + (-1958)*(10) + (-1056)*(1) = 0.
-/

namespace OMA.S_oeis_a172066

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172066, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 9 →
    ∀ n : ℕ, 2 ≤ n →
      (90 * (n : ℚ) + 28 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 3) * coeff n G + (-672 - 427 * (n : ℚ) - 94 * (n : ℚ) ^ 2 - 7 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-336 - 236 * (n : ℚ) - 54 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172066
