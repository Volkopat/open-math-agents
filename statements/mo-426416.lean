import Mathlib

/-!
# A nonnegative solution after deleting one column

Ke. Fel, MathOverflow question 426416, July 2022.
https://mathoverflow.net/q/426416

There is at least one column to delete. The smaller coefficient vector is
written in the original coordinates, with zero in the deleted position.
The normal equations are imposed on precisely the retained columns.
-/

namespace OMA.S_mo_426416

theorem main :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
      (b : Fin m → ℝ) (x : Fin (n + 1) → ℝ),
      (∀ k, 0 ≤ x k) →
      A.transpose.mulVec (A.mulVec x) = A.transpose.mulVec b →
      ∃ (i : Fin (n + 1)) (y : Fin (n + 1) → ℝ),
        y i = 0 ∧ (∀ k, 0 ≤ y k) ∧
        ∀ k, k ≠ i → (A.transpose.mulVec (A.mulVec y)) k = (A.transpose.mulVec b) k := by
  sorry

end OMA.S_mo_426416
