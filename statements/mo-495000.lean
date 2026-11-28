import Mathlib

/-!
# McKay's finite powerset graph reconstruction question

Source: https://mathoverflow.net/questions/495000/a-different-powerset-graph-construction
Credit: @vlad-ds

McKay asks whether the graph of legal moves between nonempty proper vertex
subsets determines the original graph. We state his finite conjecture. The
source gives the number of subsets as two to the power of the order minus
two. This convention assumes a nonempty original graph. If graphs on zero
vertices are also allowed, orders zero and one both give an empty move graph.
-/

namespace OMA.S_mo_495000

/-- An edge moves one token across an original edge to an unoccupied vertex. -/
def fullGraph {V : Type} (G : SimpleGraph V) : SimpleGraph (Set V) where
  Adj S T := ∃ u v, G.Adj u v ∧ S \ T = {u} ∧ T \ S = {v}
  symm.symm := by
    rintro S T ⟨u, v, huv, hS, hT⟩
    exact ⟨v, u, huv.symm, hT, hS⟩
  loopless := ⟨by simp⟩

/-- Delete the empty arrangement and the fully occupied arrangement. -/
def powersetGraph {V : Type} (G : SimpleGraph V) :=
  (fullGraph G).induce {S | S ≠ ∅ ∧ S ≠ Set.univ}

/-- For finite nonempty graphs, the unlabeled move graph determines the original. -/
theorem main : ∀ {V W : Type} [Finite V] [Finite W] [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    Nonempty (powersetGraph G ≃g powersetGraph H) → Nonempty (G ≃g H) := by
  sorry

end OMA.S_mo_495000
