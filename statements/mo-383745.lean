import Mathlib

/-!
# MathOverflow 383745

Source: https://mathoverflow.net/questions/383745
-/

namespace OMA.S_mo_383745

open Finset

noncomputable def quadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

def SymmetricPSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M.IsSymm ∧ ∀ v, 0 ≤ quadratic M v

noncomputable def entryArcsine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => Real.arcsin (M i j)

theorem main : ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ),
    SymmetricPSD X → (∀ i, X i i = 1) →
      ∃ a : ℝ, 0 < a ∧ SymmetricPSD (a • X - entryArcsine X) := by
  sorry

end OMA.S_mo_383745
