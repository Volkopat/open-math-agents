import Mathlib

/-!
# Subgraph of large average degree and large girth

Source: https://www.openproblemgarden.org/op/subgraph_of_large_average_degree_and_large_average_degree
Credit: @ishaanzee

**Conjecture** (C. Thomassen). For all positive integers `g` and `k`, there exists an integer `d`
such that every graph of average degree at least `d` contains a subgraph of average degree at
least `k` and girth greater than `g`.

The conjecture is true for regular graphs (Alon) and for `g ≤ 4` (Kühn–Osthus).

Formalization:
* Graphs are finite simple graphs. The average degree of a graph with vertex set `V` and edge set
  `E` is `2|E| / |V|` (computed in `ℝ`).
* A subgraph is a Mathlib `SimpleGraph.Subgraph`, with nonempty vertex set; its average degree is
  `2 |H.edgeSet| / |H.verts|`, and its girth is the `egirth` (length of a shortest cycle, `⊤` if
  acyclic) of `H` viewed as a graph on its own vertices (`H.coe`).
-/

namespace OMA.S_opg_subgraph_of_large_average_degree_and_large_average_degree

/-- **Thomassen's conjecture.** -/
theorem main : ∀ g k : ℕ, 0 < g → 0 < k → ∃ d : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (d : ℝ) ≤ 2 * (G.edgeSet.ncard : ℝ) / (Fintype.card V : ℝ) →
      ∃ H : G.Subgraph, H.verts.Nonempty ∧
        (k : ℝ) ≤ 2 * (H.edgeSet.ncard : ℝ) / (H.verts.ncard : ℝ) ∧ (g : ℕ∞) < H.coe.egirth := by
  sorry

end OMA.S_opg_subgraph_of_large_average_degree_and_large_average_degree
