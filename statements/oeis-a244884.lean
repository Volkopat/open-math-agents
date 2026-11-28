import Mathlib

/-!
# A244884: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A244884
Credit: @ivillar

Status: false as stated at n = 3 and n = 4 (the left side is -3 at n = 3 and 3 at n = 4 on the OEIS
data); `main` is the corrected recurrence (n ≥ 5), which is proved.

A244884 (offset 0): expansion of (-2 + x^2 + x - x*sqrt(1-2*x-3*x^2))/(-1 + x - sqrt(1-2*x-3*x^2));
data 1, 1, 1, 2, 5, 12, 30, 76, 196, 512, 1353, ...

Conjecture (R. J. Mathar, Jan 24 2020): D-finite with recurrence
(n+2)*a(n) + (-3*n-1)*a(n-1) - n*a(n-2) + 3*(n-3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-2*x-3*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(-1 + x - S) = -2 + x^2 + x - x*S, the factor -1 + x - S having constant term -2;
a(n) = [x^n] G. On the data the left side of the recurrence is -3 at n = 3 and 3 at n = 4, and it
vanishes from n = 5 on (for example 7*12 - 16*5 - 5*2 + 6*1 = 0 at n = 5), so the recurrence is
stated for n ≥ 5.
-/

namespace OMA.S_oeis_a244884

open PowerSeries

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 3 and n = 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 3 * X ^ 2 → coeff 0 S = 1 →
    G * (-1 + X - S) = -2 + X ^ 2 + X - X * S →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ) + 2) * coeff n G + (-3 * (n : ℚ) - 1) * coeff (n - 1) G -
        (n : ℚ) * coeff (n - 2) G + 3 * ((n : ℚ) - 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a244884
