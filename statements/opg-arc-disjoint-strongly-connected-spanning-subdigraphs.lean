import Mathlib

/-!
# Arc-disjoint strongly connected spanning subdigraphs

Source: https://www.openproblemgarden.org/op/arc_disjoint_strongly_connected_spanning_subdigraphs
Credit: @ishaanzee

**Conjecture** (J. Bang-Jensen, A. Yeo). There exists an integer `k` so that every `k`-arc-connected
digraph contains a pair of arc-disjoint strongly connected spanning subdigraphs.

Formalization:
* A digraph on a finite set `V` is a loopless relation `D` (`D u v` is the arc `u → v`).
* A digraph on `V` is strongly connected if every vertex reaches every vertex by a directed path
  (`Relation.ReflTransGen`); `k`-arc-connected (`k`-arc-strong) means strongly connected after
  deleting any set of fewer than `k` arcs.
* Two arc-disjoint strongly connected spanning subdigraphs exist iff the arcs can be split into two
  classes (`c : V → V → Fin 2`) each of which forms a strongly connected digraph on all of `V`
  (unused arcs can be added to either subdigraph without destroying strong connectivity).
-/

namespace OMA.S_opg_arc_disjoint_strongly_connected_spanning_subdigraphs

/-- The digraph `D` on `V` is strongly connected. -/
def IsStrong {V : Type*} (D : V → V → Prop) : Prop := ∀ x y : V, Relation.ReflTransGen D x y

/-- **Bang-Jensen–Yeo conjecture.** -/
theorem main : ∃ k : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (D : V → V → Prop),
    (∀ v, ¬ D v v) →
    (∀ F : Finset (V × V), F.card < k → IsStrong fun a b => D a b ∧ (a, b) ∉ F) →
      ∃ c : V → V → Fin 2, ∀ i : Fin 2, IsStrong fun a b => D a b ∧ c a b = i := by
  sorry

end OMA.S_opg_arc_disjoint_strongly_connected_spanning_subdigraphs
