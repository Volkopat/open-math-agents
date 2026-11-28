import Mathlib

/-!
# Removing vertices from graphs by reductions

Source: https://math.stackexchange.com/questions/5099016/removing-vertices-from-graphs-by-reductions-a-continuation-of-an-unsolved-prob
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $G$ be a finite simple graph. A reduction consists of choosing an even-degree vertex $v$
(in the current induced subgraph), say with degree $2m$, and either all $2m$ of its neighbors
or an odd number of its neighbors, and removing $v$ together with those chosen neighbors and
all incident edges.

Prove that all vertices of $G$ can be removed after a finite number of reductions if $G$ is
connected and has at least one even-degree vertex.

Conventions:
- Reductions operate on the current vertex subset `S : Finset V`, where adjacency and degree
  are taken in the induced subgraph of `G` on `S`.
- For an isolated vertex ($2m = 0$), removing all $0$ neighbors leaves `S.erase v`.
-/

namespace OMA.S_mse_5099016

/-- One reduction step from induced vertex set `S` to `T` in a finite simple graph `G`. -/
def ReductionStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : Prop :=
  ∃ v ∈ S, ∃ U ⊆ S,
    (∀ u ∈ U, G.Adj v u) ∧
    Even (S.filter (G.Adj v)).card ∧
    (Odd U.card ∨ U = S.filter (G.Adj v)) ∧
    T = (S.erase v) \ U

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected →
      (∃ v : V, Even (G.degree v)) →
      Relation.ReflTransGen (ReductionStep G) Finset.univ ∅ := by
  sorry

end OMA.S_mse_5099016
