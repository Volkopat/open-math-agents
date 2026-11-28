import Mathlib

/-!
# A166696: A transform of A103210.

Source: https://oeis.org/A166696 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function `(1-3x+x^2-sqrt(1-14x+27x^2-14x^3+x^4))/(4x)` given in the entry.
Here `sqrt(...)` is the power series `S` over `ℚ` with `S^2 = 1 - 14 * X + 27 * X ^ 2 - 14 * X ^ 3 + X ^ 4` and constant term `1` (it is
unique), and `A` is given without division by `4 * X * A = 1 - 3 * X + X ^ 2 - S` (this determines `A`, since
`ℚ⟦X⟧` is an integral domain and `X` is not a zero divisor). The statement asserts that such
`S, A` exist and that every such pair satisfies the recurrence.

The conjecture is stated for `n >= 5`. The entry gives no range, and at `n = 4` (the first `n`
where every index is defined) the left side equals `-1`, so the recurrence holds from `n = 5` on:
Conjecture: (n+1)*a(n) +7*(-2*n+1)*a(n-1) +27*(n-2)*a(n-2) +7*(-2*n+7)*a(n-3) +(n-5)*a(n-4)=0.
-/

namespace OMA.S_oeis_a166696

open PowerSeries

/-- `S = sqrt(1 - 14 * X + 27 * X ^ 2 - 14 * X ^ 3 + X ^ 4)` and `4 * X * A = 1 - 3 * X + X ^ 2 - S`. -/
def IsGF (S A : PowerSeries ℚ) : Prop :=
  S ^ 2 = 1 - 14 * X + 27 * X ^ 2 - 14 * X ^ 3 + X ^ 4 ∧ constantCoeff S = 1 ∧ 4 * X * A = 1 - 3 * X + X ^ 2 - S

theorem main : (∃ S A : PowerSeries ℚ, IsGF S A) ∧
    ∀ S A : PowerSeries ℚ, IsGF S A → ∀ n : ℕ, 5 ≤ n →
      (((n : ℚ)+1)) * coeff n A +
        (7*(-2*(n : ℚ)+1)) * coeff (n - 1) A +
        (27*((n : ℚ)-2)) * coeff (n - 2) A +
        (7*(-2*(n : ℚ)+7)) * coeff (n - 3) A +
        (((n : ℚ)-5)) * coeff (n - 4) A = 0 := by
  sorry

end OMA.S_oeis_a166696
