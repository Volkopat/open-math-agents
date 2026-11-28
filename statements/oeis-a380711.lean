import Mathlib

/-!
# A380711: parity of the coefficients of A(x) = 1 + x A(x) abs(1/A(x)^3)

Source: https://oeis.org/A380711 (conjectures by Paul D. Hanna, 2025)

`a(n)` (offset 0) is the coefficient of `x^n` in the power series `A(x)` over `ℤ` satisfying
`A(x) = 1 + x*A(x)*abs(1/A(x)^3)`, where `abs(F(x))` is the series formed by the absolute
values of the coefficients of `F(x)`. Here `1/A(x)^3` is written as a power series `B` with
`A^3 * B = 1` (such a `B` is unique when it exists), and `abs` is `absPS`. The equation forces
`a(0) = 1` and expresses `a(n+1)` through `a(0), ..., a(n)`, so it determines `A` uniquely; the
statement asserts that a solution exists and that every solution satisfies both conjectures of
the entry.

Conjecture 1: `a(n) == binomial(3*n-1, n)/(3*n-1) (mod 2)` for `n >= 0`. The quotient is taken
in `ℤ`; for `n >= 1` the division is exact, and for `n = 0` the natural number subtraction gives
`binomial(0, 0) = 1 = binomial(-1, 0)`, so the quotient is `1/(-1) = -1`, as in the entry.

Conjecture 2: for `n > 0`, `a(n)` is odd iff `n = 2*A003714(k) + 1` for some `k >= 0`, where
A003714 lists the Fibbinary numbers (no two adjacent 1's in the binary representation,
starting with 0).
-/

namespace OMA.S_oeis_a380711

open PowerSeries

/-- The series of absolute values of the coefficients. -/
noncomputable def absPS (F : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => |coeff n F|

/-- `A` satisfies the defining functional equation of A380711, with `B = 1/A^3`. -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  ∃ B : PowerSeries ℤ, A ^ 3 * B = 1 ∧ A = 1 + X * A * absPS B

/-- Fibbinary numbers (A003714): no two adjacent 1's in the binary representation. -/
def Fibbinary (n : ℕ) : Prop :=
  ∀ i : ℕ, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

theorem main : (∃ A : PowerSeries ℤ, IsGF A) ∧
    ∀ A : PowerSeries ℤ, IsGF A →
      (∀ n : ℕ, coeff n A ≡ ((3 * n - 1).choose n : ℤ) / ((3 * n : ℤ) - 1) [ZMOD 2]) ∧
      (∀ n : ℕ, 0 < n → (Odd (coeff n A) ↔ ∃ k : ℕ, Fibbinary k ∧ n = 2 * k + 1)) := by
  sorry

end OMA.S_oeis_a380711
