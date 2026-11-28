import Mathlib

open FirstOrder

namespace OMA.S_mo_314643

inductive FunctionSymbol : ℕ → Type
  | add : FunctionSymbol 2
  | pair : FunctionSymbol 2

inductive RelationSymbol : ℕ → Type
  | lt : RelationSymbol 2

abbrev pairingLanguage : Language :=
  ⟨FunctionSymbol, RelationSymbol⟩

abbrev pairingStructure (pair : (ℕ × ℕ) ≃ ℕ) : pairingLanguage.Structure ℕ where
  funMap := fun {_} symbol =>
    match symbol with
    | .add => fun v => v 0 + v 1
    | .pair => fun v => pair (v 0, v 1)
  RelMap := fun {_} symbol =>
    match symbol with
    | .lt => fun v => v 0 < v 1

def HasNIP (pair : (ℕ × ℕ) ≃ ℕ) : Prop :=
  letI := pairingStructure pair
  ∀ (a b : ℕ) (φ : pairingLanguage.Formula (Fin a ⊕ Fin b)), ∃ k : ℕ,
    ¬ ∃ points : Fin k → Fin a → ℕ,
        ∀ s : Set (Fin k), ∃ y : Fin b → ℕ,
          ∀ i : Fin k, φ.Realize (Sum.elim (points i) y) ↔ i ∈ s

/-- Can the natural numbers with addition and strict order be expanded
by a bijective pairing function so that the complete theory has NIP? -/
theorem main : ∃ pair : (ℕ × ℕ) ≃ ℕ, HasNIP pair := by
  sorry

end OMA.S_mo_314643
