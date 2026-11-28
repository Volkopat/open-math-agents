import FormalConjectures.Wikipedia.BergeFulkersonConjecture

-- Reduction BergeFulkersonConjecture.berge_fulkerson_conjecture.R1 of the Berge-Fulkerson
-- conjecture: the classical split into Class 1 graphs and snarks.
-- Credit: @marcusbuffett
--
-- H1 (Class 1): every cubic graph whose edges admit a proper 3-colouring (equivalently, whose
-- line graph is 3-colourable) has six perfect matchings covering every edge exactly twice.
-- Each colour class is a perfect matching, and taking each class twice gives the cover. No
-- bridgelessness is needed here.
-- H2 (open core): the conjecture for snarks in the broad sense, i.e. bridgeless cubic graphs
-- that are not 3-edge-colourable. This is where all of the difficulty lies.

namespace OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_R1

open SimpleGraph BergeFulkersonConjecture

/-- Class 1 cubic graphs: a proper 3-edge-colouring yields a Fulkerson cover. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.lineGraph.Colorable 3 →
      ∃ M : Fin 6 → G.Subgraph, IsPerfectMatchingCover G 6 2 M

/-- Snarks: bridgeless cubic graphs that are not 3-edge-colourable. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.IsBridgeless → ¬ G.lineGraph.Colorable 3 →
      ∃ M : Fin 6 → G.Subgraph, IsPerfectMatchingCover G 6 2 M

theorem main : H1 → H2 → type_of% @BergeFulkersonConjecture.berge_fulkerson_conjecture := by
  intro h1 h2 V _ _ G _ hcub hbr
  by_cases hc : G.lineGraph.Colorable 3
  · exact h1 G hcub hc
  · exact h2 G hcub hbr hc

end OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_R1
