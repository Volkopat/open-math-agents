import Mathlib

/-!
# A380709: parity of the coefficients of A(x) = 1 + x abs(1/A(x))^3

Source: https://oeis.org/A380709 (conjecture by Paul D. Hanna, 2025)

`a(n)` (offset 0) is the coefficient of `x^n` in the power series `A(x)` over `ℤ` satisfying
`A(x) = 1 + x*abs(1/A(x))^3`, where `abs(F(x))` is the series formed by the absolute values of
the coefficients of `F(x)`. Here `1/A(x)` is written as a power series `B` with `A * B = 1`
(such a `B` is unique when it exists), and `abs` is `absPS`. The equation forces `a(0) = 1` and
expresses `a(n+1)` through `a(0), ..., a(n)`, so it determines `A` uniquely; the statement
asserts that a solution exists and that every solution has the stated parity pattern.

The conjecture: `a(n) == binomial(4*n-1, n) (mod 2)` for `n >= 0`. For `n = 0` the natural
number subtraction gives `4*0-1 = 0` and `binomial(0, 0) = 1`, which agrees with the value
`binomial(-1, 0) = 1` of the generalized binomial coefficient.
-/

namespace OMA.S_oeis_a380709

open PowerSeries

/-- The series of absolute values of the coefficients. -/
noncomputable def absPS (F : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => |coeff n F|

/-- `A` satisfies the defining functional equation of A380709, with `B = 1/A`. -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  ∃ B : PowerSeries ℤ, A * B = 1 ∧ A = 1 + X * (absPS B) ^ 3

theorem main : (∃ A : PowerSeries ℤ, IsGF A) ∧
    ∀ A : PowerSeries ℤ, IsGF A → ∀ n : ℕ,
      coeff n A ≡ ((4 * n - 1).choose n : ℤ) [ZMOD 2] := by
  sorry

end OMA.S_oeis_a380709
