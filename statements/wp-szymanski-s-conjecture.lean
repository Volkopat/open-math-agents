import Mathlib

/-!
# Szymanski's conjecture

Source: https://en.wikipedia.org/wiki/Szymanski's_conjecture
Credit: @prophetlabs

The source states: every permutation on the `n`-dimensional doubly-directed hypercube graph can be
routed with edge-disjoint paths. "That is, if the permutation σ matches each vertex v to another
vertex σ(v), then for each v there exists a path in the hypercube graph from v to σ(v) such that
no two paths for two different vertices u and v use the same edge in the same direction."

Formalization choices:
* The vertices of the `n`-dimensional hypercube are the bit strings `Fin n → Bool`; two vertices
  are adjacent when they differ in exactly one coordinate (Hamming distance `1`).
* The doubly-directed hypercube has one arc in each direction for every hypercube edge. An arc
  traversed by a walk is a `SimpleGraph.Dart` of the hypercube (an edge together with a
  direction), so "the same edge in the same direction" means the same dart. Two routes may use the
  same undirected edge in opposite directions.
* The source does not require the routes to be simple or shortest (for `n ≥ 5` some permutations
  need routes that are not shortest paths, per the source). We use walks: any walk from `v` to
  `σ v` contains a path from `v` to `σ v` that uses a subset of its darts, so requiring walks or
  paths gives equivalent statements.
* A fixed point `σ v = v` is routed by the empty walk, which uses no dart.
* The source states the conjecture for every dimension `n`; it is verified for `n ≤ 4` and open
  for `n ≥ 5`.
-/

namespace OMA.S_wp_szymanski_s_conjecture

/-- The `n`-dimensional hypercube graph: bit strings of length `n`, adjacent when they differ in
exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := hammingDist u v = 1
  symm := ⟨fun u v (h : hammingDist u v = 1) => by rwa [hammingDist_comm]⟩
  loopless := ⟨fun u (h : hammingDist u u = 1) => by simp at h⟩

/-- A permutation `σ` of the vertices of the hypercube can be routed with edge-disjoint paths:
there is a route from each vertex `v` to `σ v`, and routes of two different vertices never
traverse the same edge in the same direction. -/
def IsRoutable (n : ℕ) (σ : Equiv.Perm (Fin n → Bool)) : Prop :=
  ∃ P : ∀ v, (hypercube n).Walk v (σ v),
    ∀ u v, u ≠ v → (P u).darts.Disjoint (P v).darts

/-- **Szymanski's conjecture.** For every `n`, every permutation of the vertices of the
`n`-dimensional doubly-directed hypercube can be routed with edge-disjoint paths. -/
theorem main : ∀ n : ℕ, ∀ σ : Equiv.Perm (Fin n → Bool), IsRoutable n σ := by
  sorry

end OMA.S_wp_szymanski_s_conjecture
