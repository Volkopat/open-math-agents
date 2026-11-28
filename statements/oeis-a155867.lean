import Mathlib

/-!
# A155867: A 'Morgan Voyce' transform of the large Schroeder numbers A006318.

Source: https://oeis.org/A155867 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function `(1-3x+x^2-sqrt(1-10x+19x^2-10x^3+x^4))/(2x(1-x))` given in the entry.
Here `sqrt(...)` is the power series `S` over `ℚ` with `S^2 = 1 - 10 * X + 19 * X ^ 2 - 10 * X ^ 3 + X ^ 4` and constant term `1` (it is
unique), and `A` is given without division by `2 * X * (1 - X) * A = 1 - 3 * X + X ^ 2 - S` (this determines `A`, since
`ℚ⟦X⟧` is an integral domain and `X` is not a zero divisor). The statement asserts that such
`S, A` exist and that every such pair satisfies the recurrence.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: (n+1)*a(n) + (4-11*n)*a(n-1) + (29*n-43)*a(n-2) +(73-29*n)*a(n-3) + (11*n-40)*a(n-4) + (5-n)*a(n-5) = 0.
-/

namespace OMA.S_oeis_a155867

open PowerSeries

/-- `S = sqrt(1 - 10 * X + 19 * X ^ 2 - 10 * X ^ 3 + X ^ 4)` and `2 * X * (1 - X) * A = 1 - 3 * X + X ^ 2 - S`. -/
def IsGF (S A : PowerSeries ℚ) : Prop :=
  S ^ 2 = 1 - 10 * X + 19 * X ^ 2 - 10 * X ^ 3 + X ^ 4 ∧ constantCoeff S = 1 ∧ 2 * X * (1 - X) * A = 1 - 3 * X + X ^ 2 - S

theorem main : (∃ S A : PowerSeries ℚ, IsGF S A) ∧
    ∀ S A : PowerSeries ℚ, IsGF S A → ∀ n : ℕ, 5 ≤ n →
      (((n : ℚ)+1)) * coeff n A +
        ((4-11*(n : ℚ))) * coeff (n - 1) A +
        ((29*(n : ℚ)-43)) * coeff (n - 2) A +
        ((73-29*(n : ℚ))) * coeff (n - 3) A +
        ((11*(n : ℚ)-40)) * coeff (n - 4) A +
        ((5-(n : ℚ))) * coeff (n - 5) A = 0 := by
  sorry

end OMA.S_oeis_a155867
