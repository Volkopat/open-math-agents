import Mathlib

/-!
# Extremal problem on the number of tree endomorphisms

Source: https://www.openproblemgarden.org/op/extremal_problem_on_the_number_of_tree_endomorphism
Credit: @ishaanzee

**Conjecture** (Zhicong Lin). An endomorphism of a graph is a mapping on the vertex set of the
graph which preserves edges. Among all the `n`-vertex trees, the star with `n` vertices has the
most endomorphisms, while the path with `n` vertices has the least endomorphisms.

Formalization: trees are trees on `Fin n` (`SimpleGraph.IsTree`); endomorphisms are graph
homomorphisms `T →g T`, counted with `Nat.card`. The path is Mathlib's `pathGraph n`; the star
`starGraph n` has centre `0` adjacent to every other vertex. "Most" and "least" are stated as
`≤` comparisons with every `n`-vertex tree.
-/

namespace OMA.S_opg_extremal_problem_on_the_number_of_tree_endomorphism

/-- The star on `Fin n` with centre `0`. -/
def starGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => (x : ℕ) = 0 ∨ (y : ℕ) = 0

/-- **Lin's conjecture**: every tree on `n` vertices has at least as many endomorphisms as the path
and at most as many as the star. -/
theorem main : ∀ (n : ℕ) (T : SimpleGraph (Fin n)), T.IsTree →
    Nat.card (SimpleGraph.pathGraph n →g SimpleGraph.pathGraph n) ≤ Nat.card (T →g T) ∧
      Nat.card (T →g T) ≤ Nat.card (starGraph n →g starGraph n) := by
  sorry

end OMA.S_opg_extremal_problem_on_the_number_of_tree_endomorphism
