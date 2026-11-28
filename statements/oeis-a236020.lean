import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OMA.S_oeis_a236020

/-- `k(n) = log_{τ(n)}(σ(n)) = log(σ(n)) / log(τ(n))`. -/
noncomputable def kVal (n : ℕ) : ℝ :=
  Real.log ((∑ d ∈ n.divisors, d : ℕ) : ℝ) / Real.log ((n.divisors.card : ℕ) : ℝ)

/-- OEIS A236020 conjecture: every natural number `n ≥ 2` has a unique value of `k(n)`. -/
theorem main :
    ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → kVal m = kVal n → m = n := by
  sorry

end OMA.S_oeis_a236020
