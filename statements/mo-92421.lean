import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Relation
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Defs

namespace OMA.S_mo_92421

abbrev Plane := ℝ × ℝ

/-- A drawn edge is the trace of an arc, with its two endpoints
allowed to coincide for a loop. -/
def IsEdgeTrace (vertices edge : Set Plane) : Prop :=
  ∃ path : unitInterval → Plane,
    Continuous path ∧ Set.range path = edge ∧
      edge ∩ vertices = {path 0, path 1} ∧
      ∀ s t : unitInterval, path s = path t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)

/-- A finite graph drawn in the plane with intersections only at vertices. -/
structure PlaneGraph where
  vertices : Set Plane
  edges : Set (Set Plane)
  finiteVertices : vertices.Finite
  finiteEdges : edges.Finite
  validEdges : ∀ edge ∈ edges, IsEdgeTrace vertices edge
  disjointInteriors : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → e ∩ f ⊆ vertices

/-- An ambient deformation starts at the identity and moves the plane
by homeomorphisms at every time before the last. -/
def IsAmbientDeformation (move : unitInterval × Plane → Plane) : Prop :=
  Continuous move ∧ (∀ x : Plane, move (0, x) = x) ∧
    ∀ t : unitInterval, t ≠ 1 →
      ∃ homeo : Plane ≃ₜ Plane, ∀ x : Plane, homeo x = move (t, x)

/-- A minor step deletes edges or vertices, moves by ambient isotopy,
or collapses a non-loop edge in the plane. -/
def MinorStep (G H : PlaneGraph) : Prop :=
  (H.vertices ⊆ G.vertices ∧ H.edges ⊆ G.edges) ∨
  (∃ (move : unitInterval × Plane → Plane) (homeo : Plane ≃ₜ Plane),
    IsAmbientDeformation move ∧ (∀ x : Plane, homeo x = move (1, x)) ∧
      H.vertices = homeo '' G.vertices ∧
      H.edges = (fun edge : Set Plane => homeo '' edge) '' G.edges) ∨
  (∃ (edge : Set Plane) (move : unitInterval × Plane → Plane),
    edge ∈ G.edges ∧ (∃ x ∈ edge ∩ G.vertices, ∃ y ∈ edge ∩ G.vertices, x ≠ y) ∧
      IsAmbientDeformation move ∧
      let collapse := fun x : Plane => move (1, x)
      Topology.IsQuotientMap collapse ∧
        (∀ x y : Plane, collapse x = collapse y ↔ x = y ∨ (x ∈ edge ∧ y ∈ edge)) ∧
        H.vertices = collapse '' G.vertices ∧
        H.edges = (fun e : Set Plane => collapse '' e) '' (G.edges \ {edge}))

/-- Embedded graph minors are a well-quasi-order on finite plane graphs. -/
theorem main :
    ∀ G : ℕ → PlaneGraph, ∃ i j : ℕ, i < j ∧
      Relation.ReflTransGen MinorStep (G j) (G i) := by
  sorry

end OMA.S_mo_92421
