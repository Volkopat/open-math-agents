import Mathlib

/-!
# MathOverflow 297709

Source: https://mathoverflow.net/questions/297709
-/

namespace OMA.S_mo_297709

open Set Matrix
open scoped ComplexOrder

def BoundedDiagonalPSD (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {M | M.PosSemidef ∧ ∀ i, (M i i).re ≤ 1}

theorem main : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ),
    M ≠ 0 → M ∈ (BoundedDiagonalPSD n).extremePoints ℝ → ∀ i, M i i = 0 ∨ M i i = 1 := by
  sorry

end OMA.S_mo_297709
