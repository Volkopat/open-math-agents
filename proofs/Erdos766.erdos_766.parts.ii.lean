import FormalConjectures.ErdosProblems.«766»

/-!
Erdős 766(ii) for the forcing number in the 1964 formulation.
A graph one edge below the higher threshold can be extended by one edge.
In any copy found in the extension, at most one edge is absent from the
original graph, because the vertex embedding is injective on edges.
-/

open Erdos766 SimpleGraph
open scoped SimpleGraph

namespace Erdos766Forcing

private lemma edges_from_subset {V : Type*} {G : SimpleGraph V} {s : Set (Sym2 V)}
    (hs : s ⊆ G.edgeSet) : (fromEdgeSet s).edgeSet = s := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left]
  exact Set.disjoint_left.mpr fun _ he hd => G.not_isDiag_of_mem_edgeSet (hs he) hd

private lemma subgraph_with_edges {V : Type*} {G : SimpleGraph V} {l : ℕ}
    (hl : l ≤ G.edgeSet.ncard) : ∃ H ≤ G, H.edgeSet.ncard = l := by
  obtain ⟨s, hs, hcard⟩ := Set.exists_subset_card_eq hl
  refine ⟨fromEdgeSet s, ?_, (congrArg Set.ncard (edges_from_subset hs)).trans hcard⟩
  rwa [← edgeSet_subset_edgeSet, edges_from_subset hs]

private lemma complete_edges (n : ℕ) : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
  classical
  simpa [← Set.ncard_coe_finset] using card_edgeFinset_top_eq_card_choose_two (V := Fin n)

private lemma edge_loss {V W : Type*} [Finite V] [Finite W] {G G' : SimpleGraph V}
    {H : SimpleGraph W} (f : W ↪ V) (hH : H ≤ G'.comap f) :
    H.edgeSet.ncard ≤ (G'.edgeSet \ G.edgeSet).ncard + (G.comap f).edgeSet.ncard := by
  refine (Set.ncard_le_ncard_sdiff_add_ncard _ _).trans (Nat.add_le_add_right ?_ _)
  refine Set.ncard_le_ncard_of_injOn f.sym2Map ?_ f.sym2Map.injective.injOn
  intro e
  induction e using Sym2.ind with
  | _ a b => exact fun he => ⟨hH he.1, he.2⟩

private lemma forcing_lt {n k l l' : ℕ} (hkn : k ≤ n) (hl' : l' ≤ k.choose 2)
    (hll' : l < l') : forcingNumber n k l < forcingNumber n k l' := by
  let forces (t : ℕ) : Prop := ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = t →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l' ∧ H ⊑ G
  have hcomplete : forces (n.choose 2) := by
    intro G hG
    have htop : G = ⊤ := edgeSet_injective <|
      Set.eq_of_subset_of_ncard_le (edgeSet_mono le_top) (by rw [complete_edges, hG])
    obtain ⟨H, _, hH⟩ := subgraph_with_edges (G := (⊤ : SimpleGraph (Fin k))) (l := l')
      (by rwa [complete_edges])
    exact ⟨H, hH, htop ▸ isContained_top_iff.mpr ⟨Fin.castLEEmb hkn⟩⟩
  let m := forcingNumber n k l'
  have hm : m ≤ n.choose 2 := forcingNumber_le hcomplete
  have hforce : forces m := Nat.sInf_mem (s := {t | forces t}) ⟨n.choose 2, hcomplete⟩
  have hmpos : 0 < m := by
    by_contra! h
    obtain ⟨H, hH, hcopy⟩ := hforce ⊥ (by simp; omega)
    obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
    rw [comap_bot] at hf
    simp [le_bot_iff.mp hf] at hH
    omega
  suffices forcingNumber n k l ≤ m - 1 by omega
  apply forcingNumber_le
  intro G hG
  obtain ⟨s, hGs, hstop, hs⟩ := Set.exists_subsuperset_card_eq (edgeSet_mono (G₂ := ⊤) le_top)
    (show G.edgeSet.ncard ≤ m by omega) (by rwa [complete_edges])
  have hs' : (fromEdgeSet s).edgeSet.ncard = m := by rwa [edges_from_subset hstop]
  obtain ⟨H, hH, hcopy⟩ := hforce (fromEdgeSet s) hs'
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp hcopy
  have hsub : G ≤ fromEdgeSet s := by rwa [le_fromEdgeSet_iff]
  have hcount := edge_loss (G := G) f hf
  rw [Set.ncard_sdiff (edgeSet_mono hsub), hs', hG, hH] at hcount
  obtain ⟨K, hK, hcard⟩ := subgraph_with_edges (G := G.comap f) (l := l) (by omega)
  exact ⟨K, hcard, isContained_iff_exists_le_comap.mpr ⟨f, hK⟩⟩

private lemma sq_div_four_le_choose (k : ℕ) : k ^ 2 / 4 ≤ k.choose 2 := by
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide)]
  have h := Nat.div_mul_le_self (k ^ 2) 4
  rcases k with _ | _ | k
  · decide
  · decide
  · simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (k * k)]

end Erdos766Forcing

theorem OMA.solution : type_of% @Erdos766.erdos_766.parts.ii := by
  intro k
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  intro l _ l' hl' hll'
  exact Erdos766Forcing.forcing_lt hn (hl'.2.trans (Erdos766Forcing.sq_div_four_le_choose k)) hll'
