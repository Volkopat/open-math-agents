import Mathlib

/-!
# Coloring random subgraphs

Source: https://www.openproblemgarden.org/op/coloring_random_subgraphs
Credit: @ishaanzee

If `G` is a graph and `p ∈ [0, 1]`, let `G_p` denote a subgraph of `G` where each edge of `G` appears
in `G_p` independently with probability `p`.

**Problem** (B. Bukh). Does there exist a constant `c` so that
`𝔼(χ(G_{1/2})) > c · χ(G) / log χ(G)`?

(The answer is positive for complete graphs, and `𝔼(χ(G_{1/2})) ≥ c χ(G) / log |V(G)|` is known.)
We state the affirmative answer with a positive constant `c`.

Formalization:
* Graphs are finite simple graphs. `G_{1/2}` is uniform over the `2^|E(G)|` spanning subgraphs of
  `G`, so `𝔼(χ(G_{1/2}))` is the average of `χ(G_S)` over all edge subsets `S ⊆ E(G)`, where `G_S`
  is the graph on `V` with edge set `S`.
* Chromatic numbers of finite graphs are finite; `chromaticNumber` (in `ℕ∞`) is converted with
  `ENat.toNat`. We assume `χ(G) ≥ 2` so that `log χ(G) > 0`.
-/

namespace OMA.S_opg_coloring_random_subgraphs

/-- The expected chromatic number of `G_{1/2}`. -/
noncomputable def expectedChromaticHalf {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  (∑ S ∈ G.edgeFinset.powerset,
      ((SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).chromaticNumber.toNat : ℝ)) /
    2 ^ G.edgeFinset.card

/-- **Bukh's question**, affirmative form. -/
theorem main : ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], 2 ≤ G.chromaticNumber →
      c * (G.chromaticNumber.toNat : ℝ) / Real.log (G.chromaticNumber.toNat : ℝ) <
        expectedChromaticHalf G := by
  sorry

end OMA.S_opg_coloring_random_subgraphs
