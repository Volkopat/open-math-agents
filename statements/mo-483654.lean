import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# A cubic inequality for the sum of a nonnegative matrix

Source: https://mathoverflow.net/questions/483654
Question by River Li, CC BY-SA 4.0.
The vector `1` below is the all-ones vector. This states exactly the finite
matrix inequality in the question, including arbitrary zero entries.
-/

open scoped BigOperators Matrix

namespace OMA.S_mo_483654

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, 0 ≤ A i j) →
    ((1 : Fin n → ℝ) ⬝ᵥ (A *ᵥ 1)) ^ 3 ≤
      (n : ℝ) ^ 2 * ((1 : Fin n → ℝ) ⬝ᵥ ((Aᵀ * A * Aᵀ) *ᵥ 1)) := by
  sorry

end OMA.S_mo_483654
