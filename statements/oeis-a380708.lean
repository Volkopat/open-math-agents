import Mathlib

/-!
# A380708: parity of the coefficients of A(x) = 1 + x abs(1/A(x))^2

Source: https://oeis.org/A380708 (conjecture by Paul D. Hanna, 2025)

`a(n)` (offset 0) is the coefficient of `x^n` in the power series `A(x)` over `ℤ` satisfying
`A(x) = 1 + x*abs(1/A(x))^2`, where `abs(F(x))` is the series formed by the absolute values of
the coefficients of `F(x)`. Here `1/A(x)` is written as a power series `B` with `A * B = 1`
(such a `B` is unique when it exists), and `abs` is `absPS`. The equation forces `a(0) = 1` and
expresses `a(n+1)` through `a(0), ..., a(n)`, so it determines `A` uniquely; the statement
asserts that a solution exists and that every solution has the stated parity pattern.

The conjecture: for `n > 0`, `a(n)` is odd iff `n = 2*A003714(k) + 1` for some `k >= 0`, where
A003714 lists the Fibbinary numbers (no two adjacent 1's in the binary representation,
starting with 0).
-/

namespace OMA.S_oeis_a380708

open PowerSeries

/-- The series of absolute values of the coefficients. -/
noncomputable def absPS (F : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => |coeff n F|

/-- `A` satisfies the defining functional equation of A380708, with `B = 1/A`. -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  ∃ B : PowerSeries ℤ, A * B = 1 ∧ A = 1 + X * (absPS B) ^ 2

/-- Fibbinary numbers (A003714): no two adjacent 1's in the binary representation. -/
def Fibbinary (n : ℕ) : Prop :=
  ∀ i : ℕ, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

theorem main : (∃ A : PowerSeries ℤ, IsGF A) ∧
    ∀ A : PowerSeries ℤ, IsGF A → ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, Fibbinary k ∧ n = 2 * k + 1) := by
  sorry

end OMA.S_oeis_a380708
