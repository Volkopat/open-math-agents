import Mathlib

/-!
# A368626: parity of the coefficients of A(x) = 1 + x (A(x)^2 - A(-x)^2)/2 + x (A(x)^3 + A(-x)^3)/2

Source: https://oeis.org/A368626 (conjecture by Paul D. Hanna, Jan 2024)

`a(n)` (offset 0) is the coefficient of `x^n` in the power series `A(x)` over `ℤ` satisfying
`A(x) = 1 + x*(A(x)^2 - A(-x)^2)/2 + x*(A(x)^3 + A(-x)^3)/2`. Here `A(-x)` is
`PowerSeries.rescale (-1) A`, and the equation is multiplied by `2` to avoid division
(`ℤ⟦X⟧` has no `2`-torsion, so this is equivalent). The equation determines `A` uniquely
(it gives `a(0) = 1` and expresses `a(n+1)` through `a(0), ..., a(n)`), so the statement
asserts that a solution exists and that every solution has the stated parity pattern.

The conjecture: `a(n)` is odd when `n = 2^k - 1` for some `k >= 0`, and even elsewhere.
-/

namespace OMA.S_oeis_a368626

open PowerSeries

/-- `A` satisfies the defining functional equation of A368626 (times `2`). -/
def IsGF (A : PowerSeries ℤ) : Prop :=
  2 * A = 2 + X * (A ^ 2 - (rescale (-1 : ℤ) A) ^ 2) + X * (A ^ 3 + (rescale (-1 : ℤ) A) ^ 3)

theorem main : (∃ A : PowerSeries ℤ, IsGF A) ∧
    ∀ A : PowerSeries ℤ, IsGF A → ∀ n : ℕ, Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a368626
