import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_156846

/-- The constant as printed in the question, with the harmonic sum through `n`. -/
noncomputable def constant (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1 - ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1)) /
    ((n : ℝ) * ((n : ℝ) + 1))

/-- The right-hand side in zero-based indexing. -/
noncomputable def forcing (n i : ℕ) : ℝ :=
  1 / ((i : ℝ) + 2) - constant n

/-- The rows of the linear system and the weighted normalization. -/
def Solves (n : ℕ) (w : ℕ → ℝ) : Prop :=
  (∀ i : ℕ, i < n →
    w i - (∑ j ∈ Finset.range (i + 1), w (n - (i + 1) + j)) /
      ((i : ℝ) + 1) = forcing n i) ∧
  (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * w i) = 0

/-- Existence of a solution to the system posed in the question. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ w : ℕ → ℝ, Solves n w := by
  sorry

end OMA.S_mo_156846
