import Mathlib

/-!
# Cycle double cover conjecture

Source: https://en.wikipedia.org/wiki/cycle_double_cover_conjecture
Credit: @mattdorman

The source states: every bridgeless graph has a family of cycles that includes each edge twice
(a cycle double cover).

Reading used here: `G` is a finite simple graph with no bridge. The family is a finite list of
cycles of `G` (repetitions allowed, as in a family), and "includes each edge twice" means every
edge of `G` lies on exactly two cycles of the list, counted with multiplicity. Restricting to
simple graphs loses nothing: subdividing the edges of a multigraph keeps it bridgeless and
turns cycle double covers into cycle double covers both ways.
-/

namespace OMA.S_wp_cycle_double_cover_conjecture

open Classical in
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
      ∃ L : List (Σ v : V, G.Walk v v), (∀ c ∈ L, c.2.IsCycle) ∧
        ∀ e ∈ G.edgeSet, (L.filter fun c => decide (e ∈ c.2.edges)).length = 2 := by
  sorry

end OMA.S_wp_cycle_double_cover_conjecture
