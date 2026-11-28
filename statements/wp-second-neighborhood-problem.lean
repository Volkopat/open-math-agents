import Mathlib

/-!
# Second neighborhood problem

Source: https://en.wikipedia.org/wiki/second_neighborhood_problem
Credit: @mattdorman

The source asks (Seymour's second neighborhood conjecture): does every oriented graph contain a
vertex for which there are at least as many other vertices at distance two as at distance one?

Reading used here: the standard form of the conjecture, for finite oriented graphs with at least
one vertex. An oriented graph is a relation `A` (arcs `v → w`) that is irreflexive and has no
pair of opposite arcs. Distances are directed out-distances: the vertices at distance one from
`v` are its out-neighbours, and those at distance two are the vertices `w ≠ v` that are not
out-neighbours of `v` but are reached by a directed path `v → u → w`. The statement below is the
affirmative answer.
-/

namespace OMA.S_wp_second_neighborhood_problem

/-- Vertices at out-distance one from `v`. -/
def firstOut {V : Type} (A : V → V → Prop) (v : V) : Set V := {w | A v w}

/-- Vertices at out-distance exactly two from `v`. -/
def secondOut {V : Type} (A : V → V → Prop) (v : V) : Set V :=
  {w | w ≠ v ∧ ¬ A v w ∧ ∃ u, A v u ∧ A u w}

theorem main :
    ∀ (V : Type) [Fintype V] [Nonempty V] (A : V → V → Prop),
      (∀ v, ¬ A v v) → (∀ v w, A v w → ¬ A w v) →
        ∃ v, (firstOut A v).ncard ≤ (secondOut A v).ncard := by
  sorry

end OMA.S_wp_second_neighborhood_problem
