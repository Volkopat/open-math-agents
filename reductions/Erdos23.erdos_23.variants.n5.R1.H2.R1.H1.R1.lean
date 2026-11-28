import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1

/-!
Separate the degree-12 vertices whose induced core is bipartite
with at least 28 edges and at most 53 edges to the root's neighborhood.
-/

open SimpleGraph Finset
open scoped Classical

namespace OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
    (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
    93 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 12) →
    (∀ v, 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card) →
    (∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) →
    (∀ v, G.degree v = 12 →
      let H := G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))
      H.IsBipartite → H.edgeFinset.card < 28 ∨ 65 + H.edgeFinset.card < G.edgeFinset.card) →
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
    ∀ v, G.degree v = 12 →
      let H := G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))
      H.IsBipartite → 28 ≤ H.edgeFinset.card → G.edgeFinset.card ≤ 65 + H.edgeFinset.card →
      ∃ S : Finset (Fin 25),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H1 := by
  intro rest good G _ triangleFree maximal common lo hi degrees neighbor pair
  by_cases useful : ∃ v, G.degree v = 12 ∧
      let H := G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))
      H.IsBipartite ∧ 28 ≤ H.edgeFinset.card ∧ G.edgeFinset.card ≤ 65 + H.edgeFinset.card
  · obtain ⟨v, hv, bipartite, dense, range⟩ := useful
    exact good G triangleFree common v hv bipartite dense range
  · apply rest G triangleFree maximal common lo hi degrees neighbor pair
    intro v hv
    dsimp only
    intro bipartite
    by_contra! bad
    exact useful ⟨v, hv, bipartite, bad.1, bad.2⟩

end OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1_H1_R1