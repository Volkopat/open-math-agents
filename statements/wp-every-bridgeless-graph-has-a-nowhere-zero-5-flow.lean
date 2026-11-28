import Mathlib

/-!
# Every bridgeless graph has a nowhere-zero 5-flow

Source: https://en.wikipedia.org/wiki/nowhere-zero_flows
Credit: @mattdorman

The source states Tutte's 5-flow conjecture: every bridgeless graph has a nowhere-zero 5-flow.

Reading used here: `G` is a finite simple graph with no bridge. A nowhere-zero `5`-flow is an
orientation of the edges with integer values in `{±1, …, ±4}` such that at every vertex the
inflow equals the outflow. It is encoded as an antisymmetric function `f : V → V → ℤ`
(`f u v` is the flow from `u` to `v` along the edge `uv`, so `f v u = -f u v`), zero off the
edges, with `0 < |f u v| < 5` on every edge and `∑_v f u v = 0` at every vertex `u`.
Restricting to simple graphs loses nothing: subdividing edges of a multigraph keeps it
bridgeless and preserves nowhere-zero flows both ways, and loops carry any nonzero value.
-/

namespace OMA.S_wp_every_bridgeless_graph_has_a_nowhere_zero_5_flow

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
      ∃ f : V → V → ℤ, (∀ u v, f v u = -f u v) ∧
        (∀ u v, ¬ G.Adj u v → f u v = 0) ∧
        (∀ u v, G.Adj u v → 0 < |f u v| ∧ |f u v| < 5) ∧
        ∀ u, ∑ v, f u v = 0 := by
  sorry

end OMA.S_wp_every_bridgeless_graph_has_a_nowhere_zero_5_flow
