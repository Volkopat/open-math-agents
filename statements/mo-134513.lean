import Mathlib

/-!
# Graphs with constant edge imbalance

Felix Goldberg asks whether a finite simple graph whose edges all have the
same absolute difference of endpoint degrees must be regular or isomorphic
to the three-vertex path. The question as posted does not assume connectivity.

Source: https://mathoverflow.net/questions/134513/graphs-with-constant-edge-imbalance
Credit: @chuyeow
-/

namespace OMA.S_mo_134513

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∃ k : ℕ, ∀ u v : V, G.Adj u v → Nat.dist (G.degree u) (G.degree v) = k) →
    (∃ d : ℕ, G.IsRegularOfDegree d) ∨ Nonempty (G ≃g SimpleGraph.pathGraph 3) := by
  sorry

end OMA.S_mo_134513
