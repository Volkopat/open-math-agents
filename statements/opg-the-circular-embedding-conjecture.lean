import Mathlib

/-!
# The circular embedding conjecture

Source: https://www.openproblemgarden.org/op/the_circular_embedding_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Haggard): every 2-connected graph may be embedded in a surface so that the boundary
of each face is a cycle.

Conventions:
* Graphs are finite simple graphs. 2-connected: at least 3 vertices, connected, and still
  connected after deleting any one vertex.
* An embedding in a closed surface all of whose faces are bounded by cycles is encoded
  combinatorially, as is standard (and as in the source's own argument for cubic graphs): a
  finite family of cycles of `G` (the face boundaries, repetitions allowed) covering every edge
  exactly twice, such that the surface obtained by gluing a disc to each cycle is a surface at
  every vertex, i.e. the link of each vertex `v` is a single cycle. The link of `v` has the edges
  at `v` as vertices and one edge for each face corner at `v` (the two edges of a face cycle
  through `v`); with the double cover it is 2-regular, so it is a single cycle iff it is
  connected. Conversely every cellular embedding with all faces bounded by cycles gives such a
  family.
-/

namespace OMA.S_opg_the_circular_embedding_conjecture

/-- 2-connectivity of a finite simple graph. -/
def TwoConnected {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧ ∀ v : V, (G.induce {v}ᶜ).Connected

/-- Two edges `e f` at `v` are consecutive at a corner of the face cycle `face i`. -/
def CornerAdj {V : Type} {G : SimpleGraph V} {k : ℕ} (face : Fin k → Σ u : V, G.Walk u u)
    (v : V) (e f : Sym2 V) : Prop :=
  ∃ i : Fin k, e ≠ f ∧ v ∈ e ∧ v ∈ f ∧ e ∈ (face i).2.edges ∧ f ∈ (face i).2.edges

/-- `G` has an embedding in a closed surface in which every face is bounded by a cycle. -/
def HasCircularEmbedding {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (face : Fin k → Σ u : V, G.Walk u u),
    (∀ i, (face i).2.IsCycle) ∧
    (∀ e ∈ G.edgeSet, {i : Fin k | e ∈ (face i).2.edges}.ncard = 2) ∧
    (∀ v : V, ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, v ∈ e → v ∈ f →
      Relation.ReflTransGen (CornerAdj face v) e f)

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), TwoConnected G → HasCircularEmbedding G := by
  sorry

end OMA.S_opg_the_circular_embedding_conjecture
