import Mathlib

/-!
# Minimal graphs with a prescribed number of spanning trees

Source: https://www.openproblemgarden.org/op/minimal_graphs_with_a_prescribed_number_of_spanning_trees
Credit: @ishaanzee

**Conjecture** (J. Azarija, R. Škrekovski). Let `n ≥ 3` be an integer and let `α(n)` denote the
least integer `k` such that there exists a simple graph on `k` vertices having precisely `n`
spanning trees. Then `α(n) = o(log n)`.

`α(n)` is well defined for `n ≥ 3` since the cycle `C_n` has `n` spanning trees.

Formalization:
* A spanning tree of a simple graph `G` on `Fin k` is a set `T` of edges of `G` such that the
  graph on `Fin k` with edge set `T` is a tree (`SimpleGraph.IsTree`: connected and acyclic, on
  all `k` vertices). `numSpanningTrees G` counts these sets (`Set.ncard`; the set is finite).
* `α(n)` is the least `k` (`sInf`) such that some simple graph on `Fin k` has exactly `n`
  spanning trees.
* `α(n) = o(log n)` is Mathlib's little-o as `n → ∞`; only large `n` matter, so the restriction
  `n ≥ 3` is automatic.
-/

namespace OMA.S_opg_minimal_graphs_with_a_prescribed_number_of_spanning_trees

/-- The number of spanning trees of a simple graph `G` on `Fin k`. -/
noncomputable def numSpanningTrees {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ :=
  {T : Set (Sym2 (Fin k)) | T ⊆ G.edgeSet ∧ (SimpleGraph.fromEdgeSet T).IsTree}.ncard

/-- `α(n)`: the least number of vertices of a simple graph with exactly `n` spanning trees. -/
noncomputable def α (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ G : SimpleGraph (Fin k), numSpanningTrees G = n}

/-- **Azarija–Škrekovski conjecture**: `α(n) = o(log n)`. -/
theorem main : (fun n : ℕ => (α n : ℝ)) =o[Filter.atTop] (fun n : ℕ => Real.log n) := by
  sorry

end OMA.S_opg_minimal_graphs_with_a_prescribed_number_of_spanning_trees
