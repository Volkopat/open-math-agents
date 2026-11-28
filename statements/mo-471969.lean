import Mathlib

/-!
# Diagonal cofactors of an odd-order symmetric zero-one matrix

Source: user528497, https://mathoverflow.net/questions/471969 (CC BY-SA 4.0).
Credit: @connoranderson.

The source asks whether the universal assertion below is true. The
cofactor matrix is the transpose of the adjugate, with the same diagonal.
-/

namespace OMA.S_mo_471969

theorem main :
    ∀ (n : ℕ), Odd n → ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm →
      (∀ i j, A i j = 0 ∨ A i j = 1) → (∀ i, A i i = 0) → A.det ≠ 0 →
      ∃ i, A.adjugate i i ≠ 0 := by
  sorry

end OMA.S_mo_471969
