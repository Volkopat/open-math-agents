import Mathlib

/-!
# Conway's thrackle conjecture that thrackles cannot have more edges than vertices

Source: https://en.wikipedia.org/wiki/Conway's_thrackle_conjecture
Credit: @jarrettbranch

## The problem

A *thrackle* is an embedding of a graph in the plane in which each edge is a Jordan arc and
every pair of edges meet exactly once. Edges may either meet at a common endpoint, or, if they
have no endpoints in common, at a point in their interiors; in the latter case they must cross
at their intersection point (the intersection must be transverse).

Conway's thrackle conjecture: in any thrackle, the number of edges is at most the number of
vertices.

## Formalization notes

* The plane is `ℝ × ℝ`. Graphs are finite simple graphs `G : SimpleGraph V` with `[Finite V]`.
* A drawing places the vertices at distinct points `pos v` and draws each edge `e` as a set
  `curve e`. For an edge `s(u, v)`, `curve s(u, v)` is a Jordan arc from `pos u` to `pos v`
  (the image of a continuous injective map from `[0, 1]`) which contains no other vertex point,
  as in any embedding of a graph.
* Two distinct edges with a common endpoint `w` (in a simple graph they share at most one)
  meet only at `pos w`: their arcs intersect in exactly `{pos w}`.
* Two edges with no common endpoint intersect in exactly one point `x`, and they cross at `x`.
  This point is interior to both arcs, since an arc contains no vertex point other than its
  own endpoints.
* `CrossesAt A B x` is the standard topological notion of a transverse (crossing, not
  touching) intersection: some homeomorphism between an open neighbourhood of `x` and an open
  neighbourhood of `0` sends `x` to `0`, the points of `A` to the horizontal axis and the
  points of `B` to the vertical axis.
* The number of edges is `G.edgeSet.ncard` and the number of vertices is `Nat.card V`.
-/

namespace OMA.S_wp_conway_s_thrackle_conjecture_that_thrackles_cannot_have_more_edges_than_vertices

/-- `A` is a Jordan arc from `p` to `q`: the image of a continuous injective map from the unit
interval sending `0` to `p` and `1` to `q`. -/
def IsArcBetween (A : Set (ℝ × ℝ)) (p q : ℝ × ℝ) : Prop :=
  ∃ γ : unitInterval → ℝ × ℝ, Continuous γ ∧ Function.Injective γ ∧
    γ 0 = p ∧ γ 1 = q ∧ Set.range γ = A

/-- The sets `A` and `B` cross (transversally) at `x`: near `x`, a homeomorphism onto an open
neighbourhood of the origin takes `A` to the horizontal axis and `B` to the vertical axis. -/
def CrossesAt (A B : Set (ℝ × ℝ)) (x : ℝ × ℝ) : Prop :=
  ∃ φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), x ∈ φ.source ∧ φ x = 0 ∧
    φ '' (A ∩ φ.source) = {y | y.2 = 0} ∩ φ.target ∧
    φ '' (B ∩ φ.source) = {y | y.1 = 0} ∩ φ.target

/-- `pos` and `curve` form a thrackle drawing of `G`. -/
def IsThrackleDrawing {V : Type} (G : SimpleGraph V) (pos : V → ℝ × ℝ)
    (curve : Sym2 V → Set (ℝ × ℝ)) : Prop :=
  Function.Injective pos ∧
  -- each edge is a Jordan arc between its endpoints, through no other vertex
  (∀ u v, G.Adj u v → IsArcBetween (curve s(u, v)) (pos u) (pos v)) ∧
  (∀ u v, G.Adj u v → ∀ w, pos w ∈ curve s(u, v) → w = u ∨ w = v) ∧
  -- two edges with a common endpoint meet only there
  (∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f → ∀ w, w ∈ e → w ∈ f →
    curve e ∩ curve f = {pos w}) ∧
  -- two edges with no common endpoint meet exactly once, crossing there
  (∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, (∀ w, w ∈ e → w ∉ f) →
    ∃ x, curve e ∩ curve f = {x} ∧ CrossesAt (curve e) (curve f) x)

/-- `G` is a thrackle: it has a thrackle drawing in the plane. -/
def IsThrackle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (curve : Sym2 V → Set (ℝ × ℝ)), IsThrackleDrawing G pos curve

theorem main :
    ∀ (V : Type) [Finite V] (G : SimpleGraph V), IsThrackle G →
      G.edgeSet.ncard ≤ Nat.card V := by
  sorry

end OMA.S_wp_conway_s_thrackle_conjecture_that_thrackles_cannot_have_more_edges_than_vertices
