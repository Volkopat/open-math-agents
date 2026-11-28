import Mathlib

/-!
# A172063: Mathar's recurrence

Source: https://oeis.org/A172063
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172063 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=6;
data 1, 7, 37, 174, 771, 3300, 13820, 57044, 233108, 945793, 3817351, 15347362, ...

Conjecture (R. J. Mathar, Feb 19 2016):
2*n*(n+6)*(n+3)*a(n) -(7*n^3+59*n^2+166*n+160)*a(n-1) -2*(2*n+5)*(n+4)*(n+2)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^6;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (160)*(37) + (-784)*(7) + (-432)*(1) = 0.
-/

namespace OMA.S_oeis_a172063

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172063, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 6 →
    ∀ n : ℕ, 2 ≤ n →
      (36 * (n : ℚ) + 18 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 3) * coeff n G + (-160 - 166 * (n : ℚ) - 59 * (n : ℚ) ^ 2 - 7 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-80 - 92 * (n : ℚ) - 34 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172063
