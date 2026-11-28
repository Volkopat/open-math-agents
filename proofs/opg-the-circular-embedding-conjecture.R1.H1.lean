import OMAReductions.R_opg_the_circular_embedding_conjecture_R1
import Mathlib

/-!
This proves the cycle case of the reduction by @marcusbuffett in PR #20318.
Both faces have the spanning cycle as their boundary.
-/

open OMA.S_opg_the_circular_embedding_conjecture SimpleGraph

private lemma oma_spanning_cycle {V : Type} [Fintype V] {G : SimpleGraph V}
    (hc : TwoConnected G) (hg : G.IsCycles) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ ∀ e ∈ G.edgeSet, e ∈ p.edges := by
  classical
  obtain ⟨hcard, hconn, _⟩ := hc
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let v : V := Classical.arbitrary V
  have hn : (G.neighborSet v).Nonempty := hconn.preconnected.exists_adj_of_nontrivial v
  obtain ⟨p, hp, hverts⟩ := hg.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (v := v) (c := G.connectedComponentMk v) rfl hn
  refine ⟨v, p, hp, ?_⟩
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
    intro hab
    have ha : a ∈ p.toSubgraph.verts := hverts.symm ▸
      ConnectedComponent.sound (hconn.preconnected a v)
    exact Walk.adj_toSubgraph_iff_mem_edges.mp
      ((hp.adj_toSubgraph_iff_of_isCycles hg ha b).mpr hab)

private lemma oma_two_faces {V : Type} {G : SimpleGraph V} {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hall : ∀ e ∈ G.edgeSet, e ∈ p.edges) : HasCircularEmbedding G := by
  let face : Fin 2 → Σ u : V, G.Walk u u := fun _ => ⟨v,p⟩
  refine ⟨2, face, fun _ => hp, ?_, ?_⟩
  · intro e he
    have hu : {i : Fin 2 | e ∈ (face i).2.edges} = Set.univ := by
      ext i
      simp [face,hall e he]
    simp [hu]
  · intro w e he f hf hwe hwf
    by_cases h : e = f
    · subst f
      exact .refl
    · exact .single ⟨0, h, hwe, hwf, hall e he, hall f hf⟩

theorem OMA.solution : OMA.R_opg_the_circular_embedding_conjecture_R1.H1 := by
  intro V _ G hc hg
  obtain ⟨v, p, hcycle, hall⟩ := oma_spanning_cycle hc hg
  exact oma_two_faces hcycle hall
