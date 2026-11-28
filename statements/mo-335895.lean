import Mathlib

/-!
# MathOverflow 335895

Source: https://mathoverflow.net/questions/335895
-/

namespace OMA.S_mo_335895

/-- The equivalence classes of positions contain the transpose of every member. -/
def SymmetricBlocks (n : ℕ) (blocks : Setoid (Fin n × Fin n)) : Prop :=
  ∀ i j, blocks.r (i, j) (j, i)

/-- An admissible matrix is symmetric, constant on classes, and gives different
colors to distinct classes that meet in a row or a column. -/
def IsBlockColoring (n : ℕ) (blocks : Setoid (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Prop :=
  (∀ i j, color (i, j) = color (j, i)) ∧
    (∀ x y, blocks.r x y → color x = color y) ∧
    (∀ x y, (x.1 = y.1 ∨ x.2 = y.2) → color x = color y → blocks.r x y)

theorem main : ∀ (n : ℕ) (blocks : Setoid (Fin n × Fin n)),
    SymmetricBlocks n blocks → ∃ color, IsBlockColoring n blocks color := by
  sorry

end OMA.S_mo_335895
