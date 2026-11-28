import Mathlib

/-!
# Bounding the chromatic number of triangle-free graphs with fixed maximum degree

Source: http://www.openproblemgarden.org/op/bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree
Credit: @shc261392

Conjecture (Kostochka and Reed): a triangle-free graph with maximum degree `Δ` has chromatic
number at most `⌈Δ / 2⌉ + 2`.

Reading used here:
* Graphs are finite simple graphs; `Δ` is `G.maxDegree`; triangle-free is `G.CliqueFree 3`.
* `⌈Δ / 2⌉` is written `(Δ + 1) / 2` in natural-number division.
-/

namespace OMA.S_opg_bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.CliqueFree 3 →
      G.chromaticNumber ≤ (((G.maxDegree + 1) / 2 + 2 : ℕ) : ℕ∞) := by
  sorry

end OMA.S_opg_bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree
