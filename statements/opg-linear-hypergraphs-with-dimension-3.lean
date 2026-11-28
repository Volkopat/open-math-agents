import Mathlib

/-!
# Linear hypergraphs of incidence dimension at most three

De Fraysseix, Ossona de Mendez and Rosenstiehl conjecture that a finite linear
hypergraph whose incidence poset has dimension at most three has a representation
by intersections of triangles and straight line segments in the plane.

The paper allows singleton edges. Each edge therefore gets a point belonging to
exactly its incident shapes. At every point covered by shapes, the vertices of
all the shapes there must belong to one edge. For edges of size at least two,
linearity makes them precisely the maximal intersecting families of that size.

* H. de Fraysseix, P. Ossona de Mendez and P. Rosenstiehl,
  *Representation of Planar Hypergraphs by Contacts of Triangles*,
  Graph Drawing 2007, LNCS 4875, pp. 125–136. See §1.1 and §4, Conjecture 2
  on p. 135. https://doi.org/10.1007/978-3-540-77537-9_15
* Source: https://www.openproblemgarden.org/op/linear_hypergraphs_with_dimension_3

Credit: @studer
-/

namespace OMA.S_opg_linear_hypergraphs_with_dimension_3

abbrev Plane := ℝ × ℝ

/-- Strict comparison in the incidence poset on the disjoint union of vertices and edges. -/
def incidenceLT {V : Type*} (H : Hypergraph V) :
    H.vertexSet ⊕ H.edgeSet → H.vertexSet ⊕ H.edgeSet → Prop
  | .inl v, .inr e => v.val ∈ e.val
  | _, _ => False

/-- Ranks in three linear extensions. An extension can be repeated if fewer suffice. -/
def dimensionAtMostThree {V : Type*} (H : Hypergraph V) : Prop :=
  ∃ rank : Fin 3 → (H.vertexSet ⊕ H.edgeSet) ↪ ℕ,
    ∀ a b, incidenceLT H a b ↔ ∀ i, rank i a < rank i b

/-- A closed straight segment of positive length or a filled nondegenerate triangle. -/
def isTriangleOrSegment (s : Set Plane) : Prop :=
  (∃ a b : Plane, a ≠ b ∧ s = segment ℝ a b) ∨
  ∃ v : Fin 3 → Plane, AffineIndependent ℝ v ∧ s = convexHull ℝ (Set.range v)

/-- Each edge has an exact point of incidence, and every common intersection is
accounted for by a hyperedge. -/
def hasIntersectionRepresentation {V : Type*} (H : Hypergraph V) : Prop :=
  ∃ shape : H.vertexSet ↪ Set Plane,
    (∀ v, isTriangleOrSegment (shape v)) ∧
    (∀ e : H.edgeSet, ∃ z : Plane, ∀ v : H.vertexSet, z ∈ shape v ↔ v.val ∈ e.val) ∧
    ∀ z : Plane, (∃ v, z ∈ shape v) →
      ∃ e : H.edgeSet, ∀ v : H.vertexSet, z ∈ shape v → v.val ∈ e.val

theorem main : ∀ {V : Type*} (H : Hypergraph V),
    H.vertexSet.Finite →
    (∀ e ∈ H.edgeSet, e.Nonempty) →
    ⋃₀ H.edgeSet = H.vertexSet →
    (∀ e ∈ H.edgeSet, ∀ f ∈ H.edgeSet, e ≠ f → (e ∩ f).Subsingleton) →
    dimensionAtMostThree H → hasIntersectionRepresentation H := by
  sorry

end OMA.S_opg_linear_hypergraphs_with_dimension_3
