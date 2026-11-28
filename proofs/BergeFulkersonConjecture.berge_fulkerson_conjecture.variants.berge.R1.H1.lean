import OMAReductions.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_berge_R1

namespace OMA.Proof_BergeFulkerson_berge_R1_H1

open SimpleGraph BergeFulkersonConjecture

private def colorSubgraph {V : Type} (G : SimpleGraph V) (c : G.lineGraph.Coloring (Fin 3))
    (j : Fin 3) : G.Subgraph where
  verts := Set.univ
  Adj u v := ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = j
  adj_sub h := h.1
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun u v h => by
    obtain ⟨huv, hc⟩ := h
    refine ⟨huv.symm, ?_⟩
    have heq : (⟨s(v, u), huv.symm⟩ : G.edgeSet) = ⟨s(u, v), huv⟩ :=
      Subtype.ext Sym2.eq_swap
    rw [heq, hc]⟩

private lemma colorSubgraph_isPerfectMatching {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcub : IsCubic G)
    (c : G.lineGraph.Coloring (Fin 3)) (j : Fin 3) :
    (colorSubgraph G c j).IsPerfectMatching := by
  refine ⟨?_, fun _ => Set.mem_univ _⟩
  intro v _
  let f : G.neighborFinset v → Fin 3 :=
    fun w => c ⟨s(v, w.1), (G.mem_neighborFinset v w.1).mp w.2⟩
  have hf_inj : Function.Injective f := by
    intro w1 w2 hfeq
    by_contra hne
    have hne_val : w1.1 ≠ w2.1 := fun h => hne (Subtype.ext h)
    have he1 : G.Adj v w1.1 := (G.mem_neighborFinset v w1.1).mp w1.2
    have he2 : G.Adj v w2.1 := (G.mem_neighborFinset v w2.1).mp w2.2
    have hedge_ne : (⟨s(v, w1.1), he1⟩ : G.edgeSet) ≠ ⟨s(v, w2.1), he2⟩ := by
      intro heq
      have hsym : s(v, w1.1) = s(v, w2.1) := congrArg Subtype.val heq
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨_, h12⟩ | ⟨hvw2, hvw1⟩
      · exact hne_val h12
      · exact G.ne_of_adj he2 hvw2
    have hline_adj : G.lineGraph.Adj ⟨s(v, w1.1), he1⟩ ⟨s(v, w2.1), he2⟩ := by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨hedge_ne, v, Sym2.mem_mk_left v w1.1, Sym2.mem_mk_left v w2.1⟩
    exact c.valid hline_adj hfeq
  have hcard : Fintype.card (G.neighborFinset v) = Fintype.card (Fin 3) := by
    rw [Fintype.card_coe, G.card_neighborFinset_eq_degree, hcub v, Fintype.card_fin]
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩
  obtain ⟨w, hw⟩ := hf_bij.2 j
  refine ⟨w.1, ⟨(G.mem_neighborFinset v w.1).mp w.2, hw⟩, ?_⟩
  intro u hu
  obtain ⟨hvu, hcu⟩ := hu
  have hu_mem : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hvu
  have hfeq : f ⟨u, hu_mem⟩ = f w := by
    rw [hw]
    exact hcu
  exact congrArg Subtype.val (hf_inj hfeq)

end OMA.Proof_BergeFulkerson_berge_R1_H1

theorem OMA.solution :
    OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_berge_R1.H1 := by
  intro V _ _ G _ hcub hcol
  open SimpleGraph OMA.Proof_BergeFulkerson_berge_R1_H1 in
  obtain ⟨c⟩ := hcol
  let M : Fin 5 → G.Subgraph := fun i => colorSubgraph G c ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
  refine ⟨M, fun i => colorSubgraph_isPerfectMatching G hcub c _, ?_⟩
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := he
    let j : Fin 3 := c ⟨s(u, v), huv⟩
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    change (colorSubgraph G c ⟨j.val % 3, _⟩).Adj u v
    refine ⟨huv, ?_⟩
    ext
    exact (Nat.mod_eq_of_lt j.isLt).symm
