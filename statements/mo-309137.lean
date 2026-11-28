import Mathlib

/-!
# MathOverflow 309137

Source: https://mathoverflow.net/questions/309137
-/

namespace OMA.S_mo_309137

open Finset

def AllEdgesInVees {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ x y, G.Adj x y →
    ∃ z, (G.Adj x z ∧ ¬ G.Adj y z) ∨ (G.Adj y z ∧ ¬ G.Adj x z)

def Independent {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y

noncomputable def privateNeighbors {V : Type} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (x : V) : Finset V := by
  classical
  exact univ.filter fun z => z ∉ S ∧ G.Adj z x ∧ ∀ y ∈ S, G.Adj z y → y = x

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
      letI := inst
      G.Connected ∧ AllEdgesInVees G ∧
      (∃ S : Finset V, 2 ≤ S.card ∧ Independent G S) ∧
      (∀ S : Finset V, 2 ≤ S.card → Independent G S →
        ∃ a ∈ S, n < (privateNeighbors G S a).card) := by
  sorry

end OMA.S_mo_309137
