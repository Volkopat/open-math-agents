import Mathlib

/-!
# A157125: A transform of the Catalan numbers.

Source: https://oeis.org/A157125 (conjecture by R. J. Mathar, Nov 15 2012)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function
`(1-x)*(sqrt(1+x^2+4*x^3)-sqrt(1+x^2))/(2*x^3*sqrt(1+x^2))` given in the entry (the title names no
other definition). Here `sqrt(1+x^2+4*x^3)` and `sqrt(1+x^2)` are the power series `S1`, `S2` over `ℚ`
with `S1^2 = 1 + X^2 + 4*X^3`, `S2^2 = 1 + X^2` and constant terms `1` (each is unique), and `A` is
given without division by `2*X^3*S2*A = (1-X)*(S1-S2)` (this determines `A`, since `ℚ⟦X⟧` is an
integral domain and `2*X^3*S2` is nonzero). The statement asserts that such `S1, S2, A` exist and that
every such triple satisfies the recurrence.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: (n+3)*(n-2)*a(n) -4*a(n-1) +2*(n^2-n-4)*a(n-2) +2*(2*n^2-7*n+2)*a(n-3) +(n+1)*(n-4)*a(n-4) +2*(n-1)*(2*n-7)*a(n-5)=0.
-/

namespace OMA.S_oeis_a157125

open PowerSeries

/-- `S1 = sqrt(1+x^2+4x^3)`, `S2 = sqrt(1+x^2)` and `2x^3 S2 A = (1-x)(S1-S2)`. -/
def IsGF (S1 S2 A : PowerSeries ℚ) : Prop :=
  S1 ^ 2 = 1 + X ^ 2 + 4 * X ^ 3 ∧ constantCoeff S1 = 1 ∧ S2 ^ 2 = 1 + X ^ 2 ∧
    constantCoeff S2 = 1 ∧ 2 * X ^ 3 * S2 * A = (1 - X) * (S1 - S2)

theorem main : (∃ S1 S2 A : PowerSeries ℚ, IsGF S1 S2 A) ∧
    ∀ S1 S2 A : PowerSeries ℚ, IsGF S1 S2 A → ∀ n : ℕ, 5 ≤ n →
      (((n : ℚ)+3)*((n : ℚ)-2)) * coeff n A +
        (-4) * coeff (n - 1) A +
        (2*((n : ℚ)^2-(n : ℚ)-4)) * coeff (n - 2) A +
        (2*(2*(n : ℚ)^2-7*(n : ℚ)+2)) * coeff (n - 3) A +
        (((n : ℚ)+1)*((n : ℚ)-4)) * coeff (n - 4) A +
        (2*((n : ℚ)-1)*(2*(n : ℚ)-7)) * coeff (n - 5) A = 0 := by
  sorry

end OMA.S_oeis_a157125
