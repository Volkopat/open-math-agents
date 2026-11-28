import Mathlib

/-!
# MathOverflow 236533

Source: https://mathoverflow.net/questions/236533
-/

namespace OMA.S_mo_236533

open Finset Matrix

theorem main : ∀ (n m : ℕ), 0 < n → ∀ A : Matrix (Fin n) (Fin m) ℝ,
      (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j = 1) →
        ∃ X : Matrix (Fin m) (Fin n) ℝ, (∀ i j, 0 ≤ X i j) ∧
          (∀ i, ∑ j, X i j = 1) ∧
          (∀ i j, (A * X) i i = (A * X) j j) ∧
          ∀ i j, (A * X) i j ≤ (A * X) i i := by
  sorry

end OMA.S_mo_236533
