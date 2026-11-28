import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Source: https://mathoverflow.net/questions/490214 -/

open Polynomial

namespace OMA.S_mo_490214

/-- The polynomial whose value at a natural input t is the sum of kth powers from 1 to t. -/
noncomputable def faulhaber (k : ℕ) : ℚ[X] :=
  C (((k + 1 : ℕ) : ℚ)⁻¹) *
    ((Polynomial.bernoulli (k + 1)).comp (X + 1) -
      C ((Polynomial.bernoulli (k + 1)).eval 1))

noncomputable def expectedGcd (m n : ℕ) : ℚ[X] :=
  if (m = 9 ∧ n = 10) ∨ (m = 10 ∧ n = 9) then
    X * (X + 1) * (X ^ 2 + X - 1)
  else if m % 2 = 1 ∧ n % 2 = 1 then faulhaber 3
  else if m % 2 = 0 ∧ n % 2 = 0 then faulhaber 2
  else faulhaber 1

/-- Over the rationals, compare gcds up to multiplication by a nonzero constant. -/
theorem main :
    ∀ m n : ℕ, 1 < m → 1 < n → m ≠ n →
      Associated (gcd (faulhaber m) (faulhaber n)) (expectedGcd m n) := by
  sorry

end OMA.S_mo_490214
