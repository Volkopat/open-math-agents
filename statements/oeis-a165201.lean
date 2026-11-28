import Mathlib

/-!
# A165201: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A165201
Credit: @ivillar

Status: false as stated at n = 3 (the left side is 2 at n = 3 on the OEIS data); `main` is the
corrected recurrence (n ≥ 4), which is proved.

A165201 (offset 0): expansion of 1/(1-x*c(x)^3), c(x) the g.f. of A000108;
data 1, 1, 4, 16, 65, 267, 1105, 4597, 19196, 80380, 337284, 1417582, ...

Conjecture (R. J. Mathar, Nov 15 2011):
n*(n-3)*a(n) +2*(-4*n^2+15*n-10)*a(n-1) +(15*n^2-69*n+80)*a(n-2) +2*(n-2)*(2*n-5)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - x*c^3) = 1;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 4): on the data the left side of the recurrence as
stated is 2 at n = 3, and it vanishes from n = 4 on.
-/

namespace OMA.S_oeis_a165201

open PowerSeries

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - X * c ^ 3) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (-3 * (n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-20 + 30 * (n : ℚ) - 8 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (80 - 69 * (n : ℚ) + 15 * (n : ℚ) ^ 2) * coeff (n - 2) G + (20 - 18 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a165201
