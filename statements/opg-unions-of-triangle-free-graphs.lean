import Mathlib

/-!
# Unions of triangle free graphs

Source: https://www.openproblemgarden.org/op/unions_of_triangle_free_graphs
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (Erdős and Hajnal): does there exist a graph with no subgraph isomorphic to `K₄` which
cannot be expressed as a union of `ℵ₀` triangle-free graphs? (Shelah proved that the existence of
such a graph is consistent with ZFC.)

## Encoding

* Graphs are simple graphs on an arbitrary (possibly infinite) vertex type.
* "No subgraph isomorphic to `K₄`" is `G.CliqueFree 4`.
* `G` is a union of `ℵ₀` triangle-free graphs if there are graphs `H 0, H 1, …` on the same vertex
  set, each `CliqueFree 3`, whose union (supremum) is `G`. Allowing at most countably many is the
  same as exactly `ℵ₀` many, since the empty graph is triangle-free.
* The source asks a yes/no question; `main` states the answer yes.
-/

namespace OMA.S_opg_unions_of_triangle_free_graphs

theorem main :
    ∃ (V : Type) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ¬ ∃ H : ℕ → SimpleGraph V, (∀ n, (H n).CliqueFree 3) ∧ G = ⨆ n, H n := by
  sorry

end OMA.S_opg_unions_of_triangle_free_graphs
