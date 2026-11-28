import Mathlib

/-!
# OEIS A082758: sums of squares of trinomial coefficients

Source: https://oeis.org/A082758
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ∑_k T(n, k)²`, where `T(n, k)` is the coefficient of `x^k` in `(1 + x + x²)ⁿ`.
Conjecture (Bala, 2022; marked true in the entry):
`a(n) = [xⁿ] ((1 + x + x³ + x⁴)/(1 - x)²)ⁿ`.

Conventions:
* `(1 + x + x³ + x⁴)/(1 - x)²` is computed in `ℤ⟦x⟧` (`(1 - x)²` has constant term `1`).
-/

namespace OMA.S_oeis_a082758

open PowerSeries

/-- `a(n) = ∑_k T(n, k)²`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (2 * n + 1), ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ n).coeff k ^ 2

/-- `(1 + x + x³ + x⁴)/(1 - x)²`. -/
noncomputable def F : PowerSeries ℤ := (1 + X + X ^ 3 + X ^ 4) * invOfUnit ((1 - X) ^ 2) 1

/-- `a(n) = [xⁿ] Fⁿ`. -/
theorem main : ∀ n : ℕ, a n = coeff n (F ^ n) := by
  sorry

end OMA.S_oeis_a082758
