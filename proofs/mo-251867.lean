import OMAStatements.S_mo_251867
import Mathlib

-- Problem: mo-251867, if A[K_a1, ..., K_ap] is isomorphic to B[K_b1, ..., K_bq], are A and B
-- isomorphic (and the sets of clique sizes equal)?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. K_1[K_2] and K_2[K_1, K_1] are both the complete graph on two vertices, but K_1 and K_2
-- are not isomorphic since they have different numbers of vertices.

namespace MO251867

open OMA.S_mo_251867

theorem iso : Nonempty (cliqueJoin (⊥ : SimpleGraph (Fin 1)) (fun _ => 2) ≃g
    cliqueJoin (⊤ : SimpleGraph (Fin 2)) (fun _ => 1)) := by
  refine ⟨⟨⟨fun x => ⟨x.2, (0 : Fin 1)⟩, fun y => ⟨(0 : Fin 1), y.1⟩, ?_, ?_⟩, ?_⟩⟩
  · rintro ⟨i, j⟩
    obtain rfl : i = (0 : Fin 1) := Subsingleton.elim _ _
    rfl
  · rintro ⟨i, j⟩
    have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst hj
    rfl
  · rintro ⟨i, j⟩ ⟨i', j'⟩
    obtain rfl : i = i' := Subsingleton.elim _ _
    show (⊤ : SimpleGraph (Fin 2)).Adj j j' ∨
        (j = j' ∧ (⟨j, (0 : Fin 1)⟩ : Σ _i : Fin 2, Fin 1) ≠ ⟨j', (0 : Fin 1)⟩) ↔
      (⊥ : SimpleGraph (Fin 1)).Adj i i ∨
        (i = i ∧ (⟨i, j⟩ : Σ _i : Fin 1, Fin 2) ≠ ⟨i, j'⟩)
    constructor
    · intro hadj
      right
      refine ⟨rfl, ?_⟩
      intro hab
      have hjj : j = j' := by
        simpa using hab
      subst hjj
      rcases hadj with h1 | ⟨_, h2⟩
      · exact h1.ne rfl
      · exact h2 rfl
    · rintro (h1 | ⟨_, hne⟩)
      · exact absurd rfl h1.ne
      · left
        rw [SimpleGraph.top_adj]
        intro hjj
        exact hne (by rw [hjj])

end MO251867

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_251867.main) := by
  intro h
  obtain ⟨⟨e⟩, _⟩ := h 1 2 ⊥ ⊤ (fun _ => 2) (fun _ => 1) MO251867.iso
  have hcard := Fintype.card_congr e.toEquiv
  simp at hcard
