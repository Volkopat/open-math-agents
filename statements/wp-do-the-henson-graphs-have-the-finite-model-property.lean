import Mathlib

/-!
# Do the Henson graphs have the finite model property?

Source: https://en.wikipedia.org/wiki/Henson_graph
For `n ≥ 3` the Henson graph `Hₙ` is the countable homogeneous `Kₙ`-free graph (the Fraïssé
limit of the finite `Kₙ`-free graphs). The open question is whether `Hₙ` has the finite model
property: every first-order sentence (in the language of graphs) true in `Hₙ` is true in some
nonempty finite graph. `main` states the affirmative answer.

Conventions. `IsHenson n G` says that `G` is `Kₙ`-free and has the extension property: for
every finite vertex set `A` and every `B ⊆ A` containing no `Kₙ₋₁`, some vertex outside `A` is
adjacent to exactly the vertices of `B` among `A`. A countable graph with these properties is
`Hₙ` (it is unique up to isomorphism). Graphs are structures for Mathlib's
`FirstOrder.Language.graph`; asking for a finite simple graph as the model loses nothing,
since the graph axioms can be conjoined to the sentence.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_do_the_henson_graphs_have_the_finite_model_property

open FirstOrder FirstOrder.Language

/-- `G` is `Kₙ`-free and has the extension property of the Henson graph `Hₙ`. -/
def IsHenson {V : Type*} (n : ℕ) (G : SimpleGraph V) : Prop :=
  G.CliqueFree n ∧
    ∀ A B : Finset V, B ⊆ A → (∀ s ⊆ B, ¬ G.IsNClique (n - 1) s) →
      ∃ v ∉ A, ∀ a ∈ A, (G.Adj v a ↔ a ∈ B)

theorem main :
    ∀ n : ℕ, 3 ≤ n → ∀ (V : Type) [Countable V] (G : SimpleGraph V), IsHenson n G →
      ∀ φ : Language.graph.Sentence,
        (letI := G.structure; V ⊨ φ) →
        ∃ (M : Type) (_ : Fintype M) (_ : Nonempty M) (H : SimpleGraph M), letI := H.structure; M ⊨ φ := by
  sorry

end OMA.S_wp_do_the_henson_graphs_have_the_finite_model_property
