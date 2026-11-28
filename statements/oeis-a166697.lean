import Mathlib

/-!
# A166697: A "Morgan Voyce" transform of A103210.

Source: https://oeis.org/A166697 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function `(1-3x+x^2-sqrt(1-14x+27x^2-14x^3+x^4))/(4x(1-x))` given in the entry.
Here `sqrt(...)` is the power series `S` over `ℚ` with `S^2 = 1 - 14 * X + 27 * X ^ 2 - 14 * X ^ 3 + X ^ 4` and constant term `1` (it is
unique), and `A` is given without division by `4 * X * (1 - X) * A = 1 - 3 * X + X ^ 2 - S` (this determines `A`, since
`ℚ⟦X⟧` is an integral domain and `X` is not a zero divisor). The statement asserts that such
`S, A` exist and that every such pair satisfies the recurrence.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: (n+1)*a(n) + 3*(-5*n+2)*a(n-1) + (41*n-61)*a(n-2) + (-41*n+103)*a(n-3) + 3*(5*n-18)*a(n-4) + (-n+5)*a(n-5) = 0.
-/

namespace OMA.S_oeis_a166697

open PowerSeries

/-- `S = sqrt(1 - 14 * X + 27 * X ^ 2 - 14 * X ^ 3 + X ^ 4)` and `4 * X * (1 - X) * A = 1 - 3 * X + X ^ 2 - S`. -/
def IsGF (S A : PowerSeries ℚ) : Prop :=
  S ^ 2 = 1 - 14 * X + 27 * X ^ 2 - 14 * X ^ 3 + X ^ 4 ∧ constantCoeff S = 1 ∧ 4 * X * (1 - X) * A = 1 - 3 * X + X ^ 2 - S

theorem main : (∃ S A : PowerSeries ℚ, IsGF S A) ∧
    ∀ S A : PowerSeries ℚ, IsGF S A → ∀ n : ℕ, 5 ≤ n →
      (((n : ℚ)+1)) * coeff n A +
        (3*(-5*(n : ℚ)+2)) * coeff (n - 1) A +
        ((41*(n : ℚ)-61)) * coeff (n - 2) A +
        ((-41*(n : ℚ)+103)) * coeff (n - 3) A +
        (3*(5*(n : ℚ)-18)) * coeff (n - 4) A +
        ((-(n : ℚ)+5)) * coeff (n - 5) A = 0 := by
  sorry

end OMA.S_oeis_a166697
