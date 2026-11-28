import Mathlib

/-!
# Strongly regular geodetic graphs

Source: https://en.wikipedia.org/wiki/strongly_regular_graph
Credit: @shc261392

Open problem (from the list of unsolved problems, about strongly regular graphs): do there exist
infinitely many strongly regular geodetic graphs, or any strongly regular geodetic graphs that
are not Moore graphs?

Reading used here:
* Strongly regular is Mathlib's `SimpleGraph.IsSRGWith n k ℓ μ`, for a finite graph which, as
  usual for strongly regular graphs, is connected and not complete (complete graphs are excluded
  from the definition; they would make the first question trivial).
* Geodetic: between any two vertices there is a unique shortest path, i.e. any two walks from `u`
  to `v` of length `G.dist u v` are equal.
* A Moore graph is a graph whose girth is `2 d + 1`, where `d` is its diameter.
* The two questions are joined by "or", and the first implies the second: a connected
  non-complete strongly regular graph has diameter `2`, and by the Hoffman–Singleton theorem
  there are at most four Moore graphs of diameter `2`, so infinitely many strongly regular
  geodetic graphs would include one that is not a Moore graph. The statement is therefore the
  affirmative answer to the second question: a strongly regular geodetic graph that is not a
  Moore graph exists. A proof of its negation answers both questions in the negative.
-/

namespace OMA.S_wp_strongly_regular

/-- `G` is geodetic: any two shortest walks between the same endpoints are equal. -/
def IsGeodetic {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p q : G.Walk u v), p.length = G.dist u v → q.length = G.dist u v → p = q

theorem main :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj) (n k ℓ μ : ℕ),
      G.IsSRGWith n k ℓ μ ∧ G.Connected ∧ G ≠ ⊤ ∧ IsGeodetic G ∧
        G.girth ≠ ((2 * G.diam + 1 : ℕ) : ℕ∞) := by
  sorry

end OMA.S_wp_strongly_regular
