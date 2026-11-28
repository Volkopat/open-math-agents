import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source: https://mathoverflow.net/questions/165907 -/

open scoped BigOperators

namespace OMA.S_mo_165907

/-- Uniform finite truncations of the triangular-array inequality. The infinite form for
finite right-hand side follows by applying the bound to the array of absolute values,
then taking the row cutoff to infinity and taking the outer sum. -/
theorem main : ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (u : ℕ → ℕ → ℝ),
      (∑ j ∈ Finset.Icc 1 N,
        |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| ^ p) ≤
      C * ∑ j ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc j N, |u i j|) ^ p := by
  sorry

end OMA.S_mo_165907
