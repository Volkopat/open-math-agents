import FormalConjectures.Wikipedia.BergeFulkersonConjecture

-- Reduction BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.berge.R1 of Berge's conjecture (five perfect matchings cover every edge of a
-- bridgeless cubic graph): the classical split into Class 1 graphs and snarks.
-- Credit: @marcusbuffett
--
-- H1 (Class 1): every cubic graph whose edges admit a proper 3-colouring (equivalently, whose
-- line graph is 3-colourable) has five perfect matchings whose union is the edge set. The
-- three colour classes are perfect matchings covering every edge; repeating one gives five.
-- No bridgelessness is needed here.
-- H2 (open core): the conjecture for snarks in the broad sense, i.e. bridgeless cubic graphs
-- that are not 3-edge-colourable. This is where all of the difficulty lies.

namespace OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_berge_R1

open SimpleGraph BergeFulkersonConjecture

/-- Class 1 cubic graphs: a proper 3-edge-colouring yields five covering perfect matchings. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.lineGraph.Colorable 3 →
      ∃ M : Fin 5 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet

/-- Snarks: bridgeless cubic graphs that are not 3-edge-colourable. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.IsBridgeless → ¬ G.lineGraph.Colorable 3 →
      ∃ M : Fin 5 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet

theorem main : H1 → H2 → type_of% @BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.berge := by
  intro h1 h2 V _ _ G _ hcub hbr
  by_cases hc : G.lineGraph.Colorable 3
  · exact h1 G hcub hc
  · exact h2 G hcub hbr hc

end OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_berge_R1
