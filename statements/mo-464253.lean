import Mathlib

namespace OMA.S_mo_464253

/-- The real special orthogonal group in the minimum nontrivial Monster degree. -/
abbrev SO := ↥(Matrix.specialUnitaryGroup (Fin 196883) ℝ)

/-- The order of the Monster finite simple group. -/
def monsterOrder : ℕ :=
  2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

/-- The Monster in its minimum-degree representation is a maximal proper closed subgroup. -/
theorem main :
    ∃ M : Subgroup SO,
      IsSimpleGroup M ∧ Nat.card M = monsterOrder ∧
        IsClosed (M : Set SO) ∧ M ≠ ⊤ ∧
        ∀ H : Subgroup SO, M ≤ H → IsClosed (H : Set SO) → H = M ∨ H = ⊤ := by
  sorry

end OMA.S_mo_464253
