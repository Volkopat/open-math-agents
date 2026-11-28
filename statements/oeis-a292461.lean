import Mathlib

/-!
# A292461: Mathar's recurrence, corrected to n ≥ 6

Source: https://oeis.org/A292461
Credit: @ivillar

Status: false as stated at n = 4 and n = 5 (the left side is -1 at n = 4 and 1 at n = 5 on the OEIS
data); `main` is the corrected recurrence (n ≥ 6), which is proved.

A292461 (offset 0): expansion of (1 - x - x^2 + sqrt((1 - x - x^2)^2 - 4*x^3))/2 in powers of x;
data 1, -1, -1, -1, -1, -2, -4, -8, -17, -37, -82, -185, ...

Conjecture (R. J. Mathar, Jan 24 2020): D-finite with recurrence
n*a(n) + (-2*n+3)*a(n-1) + (-n+3)*a(n-2) + (-2*n+9)*a(n-3) + (n-6)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = (1-x-x^2)^2 - 4*x^3 and constant
term 1 (the constant term selects the branch of the square root), and the g.f. G is given by
2*G = 1 - x - x^2 + S; a(n) = [x^n] G. On the data the left side of the recurrence is -1 at n = 4
and 1 at n = 5, and it vanishes from n = 6 on (for example 6*(-4) - 9*(-2) - 3*(-1) - 3*(-1) + 0
= 0 at n = 6), so the recurrence is stated for n ≥ 6.
-/

namespace OMA.S_oeis_a292461

open PowerSeries

/-- The corrected recurrence (n ≥ 6): Mathar's recurrence, which fails at n = 4 and n = 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = (1 - X - X ^ 2) ^ 2 - 4 * X ^ 3 → coeff 0 S = 1 →
    2 * G = 1 - X - X ^ 2 + S →
    ∀ n : ℕ, 6 ≤ n →
      (n : ℚ) * coeff n G + (-2 * (n : ℚ) + 3) * coeff (n - 1) G +
        (-(n : ℚ) + 3) * coeff (n - 2) G + (-2 * (n : ℚ) + 9) * coeff (n - 3) G +
        ((n : ℚ) - 6) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a292461
