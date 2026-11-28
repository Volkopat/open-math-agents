import Mathlib

/-!
# Erdős–Gyárfás conjecture on cycles with power-of-two lengths

Source: https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Gy%C3%A1rf%C3%A1s_conjecture
Credit: @shc261392

The conjecture (Erdős and Gyárfás, 1995): every graph with minimum degree at least 3 contains a
simple cycle whose length is a power of two.

Reading used here:
* "graph" is a finite simple graph (`SimpleGraph V` with `[Fintype V]`); minimum degree at least
  3 is `3 ≤ G.minDegree` (for an empty vertex type `minDegree` is `0`, so the hypothesis fails).
* "simple cycle" is a closed walk with `IsCycle`; its length is the number of edges. A cycle has
  length at least 3, so the power of two is at least 4.
-/

namespace OMA.S_wp_erdos_gyarfas_conjecture_on_cycles_with_power_of_two_lengths_in_cubic_graphs

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], 3 ≤ G.minDegree →
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∃ k : ℕ, c.length = 2 ^ k := by
  sorry

end OMA.S_wp_erdos_gyarfas_conjecture_on_cycles_with_power_of_two_lengths_in_cubic_graphs
