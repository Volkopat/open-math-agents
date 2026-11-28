import Mathlib

/-!
# Cuboids with five integral distances and an integral product

The seven distances are the three edges, three face diagonals, and the
body diagonal of a rectangular cuboid. The two distances selected for
their product may also be integers, so perfect cuboids are included.

Source: https://mathoverflow.net/questions/456483
Credit: @jacklarmer
-/

namespace OMA.S_mo_456483

noncomputable def distances (a b c : ℝ) : Fin 7 → ℝ :=
  ![a, b, c, Real.sqrt (a ^ 2 + b ^ 2), Real.sqrt (a ^ 2 + c ^ 2),
    Real.sqrt (b ^ 2 + c ^ 2), Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)]

def isInteger (x : ℝ) : Prop := ∃ m : ℤ, x = (m : ℝ)

theorem main : ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    Function.Injective (distances a b c) ∧ ∃ i j : Fin 7, i ≠ j ∧
    isInteger (distances a b c i * distances a b c j) ∧
    ∀ k : Fin 7, k ≠ i → k ≠ j → isInteger (distances a b c k) := by
  sorry

end OMA.S_mo_456483
