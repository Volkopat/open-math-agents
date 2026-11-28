import Mathlib

/-!
# MathOverflow 171753

Source: https://mathoverflow.net/questions/171753
-/

namespace OMA.S_mo_171753

open Finset

structure CoHornClause (n : ℕ) where
  positive : Finset (Fin n)
  negative : Option (Fin n)

def SatisfiesCoHorn {n : ℕ} (s : Finset (Fin n)) (c : CoHornClause n) : Prop :=
  (∃ i ∈ c.positive, i ∈ s) ∨ ∃ i : Fin n, c.negative = some i ∧ i ∉ s

theorem main : ∀ (n : ℕ) (F : Set (Finset (Fin n))),
    (∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) →
      ∃ clauses : List (CoHornClause n),
        ∀ s : Finset (Fin n), (∀ c ∈ clauses, SatisfiesCoHorn s c) ↔ s ∈ F := by
  sorry

end OMA.S_mo_171753
