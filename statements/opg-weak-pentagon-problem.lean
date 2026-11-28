import Mathlib

/-!
# Weak pentagon problem

Source: https://www.openproblemgarden.org/op/weak_pentagon_problem
Credit: @ishaanzee

**Conjecture** (R. Šámal). If `G` is a cubic graph not containing a triangle, then it is possible to
color the edges of `G` by five colors, so that the complement of every color class is a bipartite
graph.

(Equivalently, `G` has a homomorphism to the Clebsch graph, or a cut-continuous map to `C₅`.)

Formalization: graphs are finite simple graphs; cubic is `IsRegularOfDegree 3` and triangle-free
is `CliqueFree 3`. An edge coloring with five colors is `c : Sym2 V → Fin 5` (only its values on
edges matter). The complement of color class `i` is the graph on `V` with the edges of `G` not
colored `i` (`G.deleteEdges`), and bipartite means 2-colorable.
-/

namespace OMA.S_opg_weak_pentagon_problem

/-- **Weak pentagon conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → G.CliqueFree 3 →
      ∃ c : Sym2 V → Fin 5, ∀ i : Fin 5, (G.deleteEdges {e | c e = i}).Colorable 2 := by
  sorry

end OMA.S_opg_weak_pentagon_problem
