import Mathlib

/-!
# A174015: A generalized Catalan number sequence.

Source: https://oeis.org/A174015 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function `(sqrt(1-2x+x^2+4x^3)+3x-1)/(2x(1-x))` given in the entry.
Here `sqrt(...)` is the power series `S` over `ℚ` with `S^2 = 1 - 2 * X + X ^ 2 + 4 * X ^ 3` and constant term `1` (it is
unique), and `A` is given without division by `2 * X * (1 - X) * A = 3 * X - 1 + S` (this determines `A`, since
`ℚ⟦X⟧` is an integral domain and `X` is not a zero divisor). The statement asserts that such
`S, A` exist and that every such pair satisfies the recurrence.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) -3*n*a(n-1) +3*(n-1)*a(n-2) +3*(n-4)*a(n-3) +2*(7-2*n)*a(n-4)=0. R. J. Mathar, Nov 13 2012
-/

namespace OMA.S_oeis_a174015

open PowerSeries

/-- `S = sqrt(1 - 2 * X + X ^ 2 + 4 * X ^ 3)` and `2 * X * (1 - X) * A = 3 * X - 1 + S`. -/
def IsGF (S A : PowerSeries ℚ) : Prop :=
  S ^ 2 = 1 - 2 * X + X ^ 2 + 4 * X ^ 3 ∧ constantCoeff S = 1 ∧ 2 * X * (1 - X) * A = 3 * X - 1 + S

theorem main : (∃ S A : PowerSeries ℚ, IsGF S A) ∧
    ∀ S A : PowerSeries ℚ, IsGF S A → ∀ n : ℕ, 4 ≤ n →
      (((n : ℚ)+1)) * coeff n A +
        (-3*(n : ℚ)) * coeff (n - 1) A +
        (3*((n : ℚ)-1)) * coeff (n - 2) A +
        (3*((n : ℚ)-4)) * coeff (n - 3) A +
        (2*(7-2*(n : ℚ))) * coeff (n - 4) A = 0 := by
  sorry

end OMA.S_oeis_a174015
