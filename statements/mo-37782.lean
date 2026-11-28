import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_37782

/-- One can delete a spanning tree of a finite, highly edge-connected graph
while losing a vanishing fraction of the guaranteed edge connectivity. -/
theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, 0 < k₀ ∧
      ∀ (k n : ℕ), k₀ ≤ k → 2 ≤ n →
      ∀ G : SimpleGraph (Fin n), G.IsEdgeConnected k →
      ∃ T : SimpleGraph (Fin n), T ≤ G ∧ T.IsTree ∧
        ∃ retained : ℕ,
          (1 - ε) * (k : ℝ) ≤ (retained : ℝ) ∧
          (G.deleteEdges T.edgeSet).IsEdgeConnected retained := by
  sorry

end OMA.S_mo_37782
