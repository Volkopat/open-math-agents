import Mathlib

/-!
# Three-chromatic (0,2)-graphs

Source: http://www.openproblemgarden.org/op/three_chromatic_0_2_graphs
Credit: @shc261392

Question (Payan): are there any (0,2)-graphs with chromatic number exactly three? A
(0,2)-graph is a graph in which every pair of distinct vertices has either `0` or `2` common
neighbours. (0,2)-graphs with chromatic number `2`, `4` and `5` are known.

Reading used here:
* Graphs are finite: the source discussion notes that an infinite three-chromatic (0,2)-graph is
  easy to construct (Payan), so the open question is about finite graphs.
* The common neighbours of `u` and `v` are `G.commonNeighbors u v`, counted with `Set.ncard`.
* The statement is the affirmative answer (such a graph exists); a proof of its negation answers
  the question in the negative.
-/

namespace OMA.S_opg_three_chromatic_0_2_graphs

theorem main :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (∀ u v : V, u ≠ v →
          (G.commonNeighbors u v).ncard = 0 ∨ (G.commonNeighbors u v).ncard = 2) ∧
        G.chromaticNumber = 3 := by
  sorry

end OMA.S_opg_three_chromatic_0_2_graphs
