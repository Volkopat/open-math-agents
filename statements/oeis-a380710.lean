import Mathlib

/-!
# A380710: parity of the coefficients of A(x) = 1 + x A(x) abs(1/A(x)^2)

Source: https://oeis.org/A380710 (conjecture by Paul D. Hanna, 2025)

`a(n)` (offset 0) is the coefficient of `x^n` in the power series `A(x)` over `ℤ` satisfying
`A(x) = 1 + x*A(x)*abs(1/A(x)^2)`, where `abs(F(x))` is the series formed by the absolute
values of the coefficients of `F(x)`. Here `1/A(x)^2` is written as a power series `B` with
`A^2 * B = 1` (such a `B` is unique when it exists), and `abs` is `absPS`. The equation forces
`a(0) = 1` and expresses `a(n+1)` through `a(0), ..., a(n)`, so it determines `A` uniquely; the
statement asserts that a solution exists and that every solution has the stated parity pattern.

The conjecture: for `n > 0`, `a(n)` is odd iff `n` is a power of 2.
-/

namespace OMA.S_oeis_a380710

open PowerSeries

/-- The series of absolute values of the coefficients. -/
noncomputable def absPS (F : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => |coeff n F|

/-- `A` satisfies the defining functional equation of A380710, with `B = 1/A^2`. -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  ∃ B : PowerSeries ℤ, A ^ 2 * B = 1 ∧ A = 1 + X * A * absPS B

theorem main : (∃ A : PowerSeries ℤ, IsGF A) ∧
    ∀ A : PowerSeries ℤ, IsGF A → ∀ n : ℕ, 0 < n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a380710
