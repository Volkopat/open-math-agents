import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1

/-!
Split the 25-vertex residual by maximum degree. A degree-13 root
leaves an induced graph on eleven vertices after removing itself and
its neighborhood. The two high-degree hypotheses distinguish whether
that induced graph is bipartite.
-/

open SimpleGraph Finset
open scoped Classical

namespace OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1

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
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    93 ≤ G.edgeFinset.card →
    ∀ v, G.degree v = 13 →
      25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
        (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card →
      (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).IsBipartite →
      ∃ S : Finset (Fin 25),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

def H3 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    ∀ v, G.degree v = 13 →
      25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
        (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card →
      ¬ (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).IsBipartite →
      ∃ S : Finset (Fin 25),
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

theorem main : H1 → H2 → H3 → OMA.R_Erdos23_erdos_23_variants_n5_R1.H2 := by
  intro low bipartite nonbipartite G _ triangleFree maximal common lo hi degree neighbor pair
  by_cases exists13 : ∃ v, G.degree v = 13
  · obtain ⟨v, hv⟩ := exists13
    by_cases core : (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).IsBipartite
    · exact bipartite G triangleFree lo v hv (neighbor v) core
    · exact nonbipartite G triangleFree v hv (neighbor v) core
  · apply low G triangleFree maximal common lo hi _ neighbor pair
    intro v
    have upper := degree v
    have ne13 : G.degree v ≠ 13 := fun hv => exists13 ⟨v, hv⟩
    omega

end OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1