import Mathlib

/-!
# A374571: parity of the coefficients of A(x) = A(x^2) - x A(x^2)^2

Source: https://oeis.org/A374571 (conjecture by Paul D. Hanna, 2024)

`a(n)` (offset 0) is the coefficient of `x^n` in the power series `A(x)` over `ℤ` satisfying
`A(x) = A(x^2) - x*A(x^2)^2`, normalized by `a(0) = 1` (the equation leaves the constant term
free, and the OEIS data starts with `a(0) = 1`). Here `A(x^2)` is `A.subst (X^2)`. With this
normalization the equation determines `A` uniquely (`a(2n) = a(n)` and
`a(2n+1) = -Sum_{k=0..n} a(k) a(n-k)`), so the statement asserts that a solution exists and
that every solution has the stated parity pattern.

The conjecture: for `n > 0`, `a(n)` is odd iff `n` is a Fibbinary number (A003714), i.e. the
binary representation of `n` contains no two adjacent 1's.
-/

namespace OMA.S_oeis_a374571

open PowerSeries

/-- `A` satisfies the defining functional equation of A374571, with `a(0) = 1`. -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 1 ∧
    A = A.subst ((X : PowerSeries ℤ) ^ 2) - X * (A.subst ((X : PowerSeries ℤ) ^ 2)) ^ 2

/-- Fibbinary numbers (A003714): no two adjacent 1's in the binary representation. -/
def Fibbinary (n : ℕ) : Prop :=
  ∀ i : ℕ, ¬ (n.testBit i = true ∧ n.testBit (i + 1) = true)

theorem main : (∃ A : PowerSeries ℤ, IsGF A) ∧
    ∀ A : PowerSeries ℤ, IsGF A → ∀ n : ℕ, 0 < n → (Odd (coeff n A) ↔ Fibbinary n) := by
  sorry

end OMA.S_oeis_a374571
