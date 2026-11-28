import Mathlib

/-!
# Coloring the union of degenerate graphs

Source: https://www.openproblemgarden.org/op/coloring_the_union_of_degenerate_graphs
Credit: @ishaanzee

**Conjecture.** The union of a `1`-degenerate graph (a forest) and a `2`-degenerate graph is
`5`-colourable.

A graph is `k`-degenerate if it can be reduced to `K₁` by repeatedly deleting vertices of degree
at most `k`. (The bound is tight: `K₅` is the union of a `1`-degenerate and a `2`-degenerate
graph.)

Formalization:
* Graphs are finite simple graphs on a common vertex set `V`; their union is `G₁ ⊔ G₂`.
* `k`-degenerate is stated in the standard equivalent form: every nonempty set `S` of vertices
  contains a vertex with at most `k` neighbours in `S`. (For a finite graph this is equivalent to
  the existence of an elimination order deleting a vertex of degree at most `k` at each step.)
* `5`-colourable is Mathlib's `Colorable 5`.
-/

namespace OMA.S_opg_coloring_the_union_of_degenerate_graphs

/-- `G` is `k`-degenerate: every nonempty vertex set has a vertex with at most `k` neighbours
inside it. -/
def IsDegenerate {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter fun w => G.Adj v w).card ≤ k

/-- **Conjecture**: the union of a forest (`1`-degenerate graph) and a `2`-degenerate graph on the
same vertex set is `5`-colourable. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj],
    IsDegenerate G₁ 1 → IsDegenerate G₂ 2 → (G₁ ⊔ G₂).Colorable 5 := by
  sorry

end OMA.S_opg_coloring_the_union_of_degenerate_graphs
