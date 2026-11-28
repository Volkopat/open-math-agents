import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Insert

/-!
# Conjecture on the preservation of unfragmented sets under element addition

Source: https://mathoverflow.net/questions/488756
Credit: @Spinausore

The commutative pair operation takes values in a totally ordered type. At a
valid deletion, the first |s|−1 pairs are exactly the pairs incident to the
deleted vertex. Equal weights allow any compatible ordering of tied pairs.
A fixed global tie-break is modeled by including its rank in the ordered value.
A singleton can be deleted without inspecting any pairs.
-/

namespace OMA.S_mo_488756

def CanDelete {α β : Type*} [DecidableEq α] [LE β]
    (w : α → α → β) (s : Finset α) (v : α) : Prop :=
  v ∈ s ∧
    ∀ x ∈ s.erase v, ∀ a ∈ s.erase v, ∀ b ∈ s.erase v, a ≠ b → w v x ≤ w a b

/-- Fragmentation means there is a complete sequence of valid deletions. -/
inductive Fragmented {α β : Type*} [DecidableEq α] [LE β]
    (w : α → α → β) : Finset α → Prop
  | empty : Fragmented w ∅
  | delete {s : Finset α} {v : α} :
      CanDelete w s v → Fragmented w (s.erase v) → Fragmented w s

theorem main : ∀ {α β : Type*} [DecidableEq α] [LinearOrder β],
    ∀ (w : α → α → β), (∀ x y, w x y = w y x) →
    ∀ (s : Finset α) (a : α), ¬ Fragmented w s → ¬ Fragmented w (insert a s) := by
  sorry

end OMA.S_mo_488756
