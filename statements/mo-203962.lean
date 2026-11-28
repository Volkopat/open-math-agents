import Mathlib

namespace OMA.S_mo_203962

/-- Distinct cells in a common row or column must have different colors. -/
def Proper {D : YoungDiagram} (color : D.cells → ℕ) : Prop :=
  ∀ a b : D.cells, a ≠ b →
    (a.val.1 = b.val.1 ∨ a.val.2 = b.val.2) → color a ≠ color b

/-- The number of cells in one color class. -/
noncomputable def frequency {D : YoungDiagram} (color : D.cells → ℕ) (i : ℕ) : ℕ :=
  ({a : D.cells | color a = i} : Set D.cells).ncard

/-- The number of cells covered by the first k color labels. -/
noncomputable def prefixCount {D : YoungDiagram} (color : D.cells → ℕ) (k : ℕ) : ℕ :=
  ({a : D.cells | color a < k} : Set D.cells).ncard

/-- Every Ferrers diagram admits a proper coloring with dominant color frequencies. -/
theorem main :
    ∀ D : YoungDiagram, ∃ color : D.cells → ℕ,
      Proper color ∧ Antitone (frequency color) ∧
        ∀ other : D.cells → ℕ, Proper other → Antitone (frequency other) →
          ∀ k : ℕ, prefixCount other k ≤ prefixCount color k := by
  sorry

end OMA.S_mo_203962
