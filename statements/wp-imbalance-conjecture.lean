import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card

/-!
# Imbalance conjecture

Source: https://en.wikipedia.org/wiki/imbalance_conjecture
Credit: @SubhanAfz
-/

namespace OMA.S_wp_imbalance_conjecture

/-- The absolute difference between the endpoint degrees. -/
noncomputable def imbalance {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ :=
  Nat.dist (G.neighborSet u).ncard (G.neighborSet v).ncard

/-- Label the vertices of the realizing simple graph by edges of the original graph.
The vertex labelled by an edge must have degree equal to that edge's imbalance. -/
theorem main :
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      (∀ u v, G.Adj u v → 0 < imbalance G u v) →
      ∃ H : SimpleGraph G.edgeSet,
        ∀ u v (h : G.Adj u v),
          (H.neighborSet ⟨s(u, v), h⟩).ncard = imbalance G u v := by
  sorry

end OMA.S_wp_imbalance_conjecture
