import Mathlib

namespace OMA.S_mo_105613

def Isomorphic {V W : Type} (A : V → V → Prop) (B : W → W → Prop) : Prop :=
  ∃ e : V ≃ W, ∀ u v : V, A u v ↔ B (e u) (e v)

def deleteVertex {V : Type} (A : V → V → Prop) (v : V) :
    {w : V // w ≠ v} → {w : V // w ≠ v} → Prop :=
  fun u w => A u.val w.val

/-- A bijection of deleted vertices matches the cards with multiplicity. -/
def HaveSameDeck {n : ℕ} (A B : Fin n → Fin n → Prop) : Prop :=
  ∃ matchCard : Equiv.Perm (Fin n), ∀ v : Fin n,
    Isomorphic (deleteVertex A v) (deleteVertex B (matchCard v))

/-- Can an acyclic digraph with at least five vertices be reconstructed
from its multiset of vertex-deleted digraphs? -/
theorem main :
    ∀ n : ℕ, 5 ≤ n → ∀ A B : Fin n → Fin n → Prop,
      WellFounded A → Std.Irrefl B → HaveSameDeck A B → Isomorphic A B := by
  sorry

end OMA.S_mo_105613
