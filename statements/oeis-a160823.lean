import Mathlib

/-!
# A160823: A transform of the large Schroeder numbers.

Source: https://oeis.org/A160823 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function `(1-x-x^2-sqrt(1-2*x-5*x^2+6*x^3+x^4))/(2*x^2*(1-x))` given in the entry.
Here `sqrt(...)` is the power series `S` over `ℚ` with `S^2 = 1 - 2 * X - 5 * X ^ 2 + 6 * X ^ 3 + X ^ 4` and constant term `1` (it is
unique), and `A` is given without division by `2 * X ^ 2 * (1 - X) * A = 1 - X - X ^ 2 - S` (this determines `A`, since
`ℚ⟦X⟧` is an integral domain and `X` is not a zero divisor). The statement asserts that such
`S, A` exist and that every such pair satisfies the recurrence.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: (n+2)*a(n) -3*(n+1)*a(n-1) +3(2-n)*a(n-2) +(11*n-20)*a(n-3) +(11-5*n)*a(n-4) + (4-n)*a(n-5)=0.
-/

namespace OMA.S_oeis_a160823

open PowerSeries

/-- `S = sqrt(1 - 2 * X - 5 * X ^ 2 + 6 * X ^ 3 + X ^ 4)` and `2 * X ^ 2 * (1 - X) * A = 1 - X - X ^ 2 - S`. -/
def IsGF (S A : PowerSeries ℚ) : Prop :=
  S ^ 2 = 1 - 2 * X - 5 * X ^ 2 + 6 * X ^ 3 + X ^ 4 ∧ constantCoeff S = 1 ∧ 2 * X ^ 2 * (1 - X) * A = 1 - X - X ^ 2 - S

theorem main : (∃ S A : PowerSeries ℚ, IsGF S A) ∧
    ∀ S A : PowerSeries ℚ, IsGF S A → ∀ n : ℕ, 5 ≤ n →
      (((n : ℚ)+2)) * coeff n A +
        (-3*((n : ℚ)+1)) * coeff (n - 1) A +
        (3*(2-(n : ℚ))) * coeff (n - 2) A +
        ((11*(n : ℚ)-20)) * coeff (n - 3) A +
        ((11-5*(n : ℚ))) * coeff (n - 4) A +
        ((4-(n : ℚ))) * coeff (n - 5) A = 0 := by
  sorry

end OMA.S_oeis_a160823
