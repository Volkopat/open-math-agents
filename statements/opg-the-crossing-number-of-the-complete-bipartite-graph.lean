import Mathlib

/-!
# The Crossing Number of the Complete Bipartite Graph (Zarankiewicz / Turán brickyard)

Source: https://www.openproblemgarden.org/op/the_crossing_number_of_the_complete_bipartite_graph
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture: `cr(K_{m,n}) = ⌊m/2⌋ ⌊(m-1)/2⌋ ⌊n/2⌋ ⌊(n-1)/2⌋`.

Drawings follow the source: vertices are distinct points of the plane, edges are arcs between
their endpoints such that (1) no edge passes through a vertex other than its endpoints,
(2) adjacent edges share only their common endpoint, (3) nonadjacent edges share at most one
point, (4) no point other than a vertex lies on three edges. The number of crossings is the
number of unordered pairs of nonadjacent edges that meet; `cr` is its minimum.

Convention notes. Edges are arbitrary arcs (continuous injective maps of `[0,1]`) rather than
polygonal lines, and the word "transversally" in (3) is not encoded; neither changes the
minimum (standard: arcs can be made polygonal, and touching points can be removed without
creating crossings). `K_{m,n}` has vertices `Fin m ⊕ Fin n` and edges `Fin m × Fin n`.
-/

namespace OMA.S_opg_the_crossing_number_of_the_complete_bipartite_graph

open Classical

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Two distinct edges of `K_{m,n}` are adjacent iff they share an endpoint. -/
def Adjacent {m n : ℕ} (e e' : Fin m × Fin n) : Prop := e.1 = e'.1 ∨ e.2 = e'.2

/-- A drawing of `K_{m,n}` in the sense of the source. -/
structure Drawing (m n : ℕ) where
  pos : Fin m ⊕ Fin n → Plane
  pos_inj : Function.Injective pos
  arc : Fin m × Fin n → unitInterval → Plane
  arc_cont : ∀ e, Continuous (arc e)
  arc_inj : ∀ e, Function.Injective (arc e)
  arc_zero : ∀ e, arc e 0 = pos (Sum.inl e.1)
  arc_one : ∀ e, arc e 1 = pos (Sum.inr e.2)
  /-- (1) no edge contains a vertex other than its endpoints -/
  no_vertex : ∀ e v, v ≠ Sum.inl e.1 → v ≠ Sum.inr e.2 → pos v ∉ Set.range (arc e)
  /-- (2) adjacent edges share only their common endpoint -/
  adjacent_meet : ∀ e e', e ≠ e' → e.1 = e'.1 →
    Set.range (arc e) ∩ Set.range (arc e') = {pos (Sum.inl e.1)}
  adjacent_meet' : ∀ e e', e ≠ e' → e.2 = e'.2 →
    Set.range (arc e) ∩ Set.range (arc e') = {pos (Sum.inr e.2)}
  /-- (3) nonadjacent edges share at most one point -/
  nonadjacent_meet : ∀ e e', ¬ Adjacent e e' →
    (Set.range (arc e) ∩ Set.range (arc e')).Subsingleton
  /-- (4) no three edges through a common non-vertex point -/
  no_triple : ∀ p : Plane, p ∉ Set.range pos → ∀ e₁ e₂ e₃,
    p ∈ Set.range (arc e₁) → p ∈ Set.range (arc e₂) → p ∈ Set.range (arc e₃) →
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃

/-- Number of crossings: unordered pairs of nonadjacent edges that meet
(ordered pairs are counted, then halved; the relation is symmetric and irreflexive). -/
noncomputable def Drawing.crossings {m n : ℕ} (D : Drawing m n) : ℕ :=
  (Finset.univ.filter fun p : (Fin m × Fin n) × (Fin m × Fin n) =>
    ¬ Adjacent p.1 p.2 ∧ (Set.range (D.arc p.1) ∩ Set.range (D.arc p.2)).Nonempty).card / 2

/-- The crossing number of `K_{m,n}`. -/
noncomputable def crK (m n : ℕ) : ℕ := sInf (Set.range (Drawing.crossings (m := m) (n := n)))

/-- Zarankiewicz's conjecture. -/
theorem main : ∀ m n : ℕ, crK m n = (m / 2) * ((m - 1) / 2) * (n / 2) * ((n - 1) / 2) := by
  sorry

end OMA.S_opg_the_crossing_number_of_the_complete_bipartite_graph
