import Mathlib

/-!
# MathOverflow 251867

Source: https://mathoverflow.net/questions/251867
-/

namespace OMA.S_mo_251867

/-- Replace a vertex by a complete graph of the specified order. -/
def cliqueJoin {p : ℕ} (A : SimpleGraph (Fin p)) (sizes : Fin p → ℕ) :
    SimpleGraph (Σ i, Fin (sizes i)) where
  Adj x y := A.Adj x.1 y.1 ∨ x.1 = y.1 ∧ x ≠ y
  symm := by
    constructor
    intro x y h
    rcases h with h | ⟨h₁, h₂⟩
    · exact Or.inl (A.adj_symm h)
    · exact Or.inr ⟨h₁.symm, h₂.symm⟩
  loopless := by
    constructor
    intro x
    simp

theorem main : ∀ (p q : ℕ) (A : SimpleGraph (Fin p)) (B : SimpleGraph (Fin q))
      (a : Fin p → ℕ) (b : Fin q → ℕ),
      Nonempty (cliqueJoin A a ≃g cliqueJoin B b) →
      Nonempty (A ≃g B) ∧ Set.range a = Set.range b := by
  sorry

end OMA.S_mo_251867
