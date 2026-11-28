import Mathlib

/-!
# Chromatic number of the graph of the permutahedron

Source: https://mathoverflow.net/questions/240260
Asked by MathOverflow user C0nn0t.

The permutahedron `Π_n` is the convex hull of all permutations of the vector
`(1, 2, ..., n)`. The question asks whether the chromatic number of its 1-skeleton
(the graph of its vertices and edges) is known. The statement below gives its value.

Translation choices.
* The vertices of `Π_n` are the `n!` vectors `(σ 0 + 1, ..., σ (n - 1) + 1)` for the
  permutations `σ` of `Fin n`, so the vertex set is `Equiv.Perm (Fin n)`.
* We use the standard combinatorial description of the edges of `Π_n`: two vertices are
  joined by an edge exactly when one is obtained from the other by exchanging two
  coordinates whose values differ by one. On permutations this means
  `τ = Equiv.swap a b * σ` with `b = a + 1`, i.e. the values `a` and `a + 1` are exchanged.
  `SimpleGraph.fromRel` symmetrizes this relation.
* The value is stated for `n ≥ 2`; for `n ≤ 1` the permutahedron is a single point.
-/

namespace OMA.S_mo_240260

/-- The 1-skeleton of the permutahedron `Π_n`, with vertex set the permutations of `Fin n`. -/
def permutahedronGraph (n : ℕ) : SimpleGraph (Equiv.Perm (Fin n)) :=
  SimpleGraph.fromRel fun σ τ => ∃ a b : Fin n, b.val = a.val + 1 ∧ τ = Equiv.swap a b * σ

theorem main : ∀ n : ℕ, 2 ≤ n → (permutahedronGraph n).chromaticNumber = 2 := by
  sorry

end OMA.S_mo_240260
