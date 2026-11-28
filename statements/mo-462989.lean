import Mathlib

/-!
# Vertices with isomorphic vertex-deleted subgraphs

Source: https://mathoverflow.net/questions/462989
Credit: @koolkao

Question (Terence C, MathOverflow 462989, 2024; CC BY-SA 4.0). Consider a simple graph `G`, and
say two vertices are conjugate if there exists an automorphism of `G` that switches them. It is
not hard to show that if `v, w` are conjugate then the induced subgraphs on `G \ v` and `G \ w` are
isomorphic. But is the converse true?

`main` states that the converse holds: for every simple graph `G` and vertices `v, w`, if the
induced subgraphs on `G \ v` and `G \ w` are isomorphic, then some automorphism of `G` maps `v`
to `w` and `w` to `v`. A disproof is a graph and two vertices for which this fails.

Translation choices:
* `G` is a `SimpleGraph V` on an arbitrary vertex type `V : Type` (no finiteness is assumed;
  the source does not ask for it). The source adds that in its own context multiple edges are
  allowed; only the simple-graph question, as posed, is stated;
* the induced subgraph on `G \ v` is `G.induce {x | x ≠ v}`, and "isomorphic" is a graph
  isomorphism `≃g` between the two induced subgraphs;
* "an automorphism of `G` that switches them" is `σ : G ≃g G` with `σ v = w` and `σ w = v`.
-/

namespace OMA.S_mo_462989

/-- If `G \ v ≅ G \ w`, then some automorphism of `G` switches `v` and `w`. -/
theorem main :
    ∀ (V : Type) (G : SimpleGraph V) (v w : V),
      Nonempty (G.induce {x | x ≠ v} ≃g G.induce {x | x ≠ w}) →
        ∃ σ : G ≃g G, σ v = w ∧ σ w = v := by
  sorry

end OMA.S_mo_462989
