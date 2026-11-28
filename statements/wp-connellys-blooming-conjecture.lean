import Mathlib

/-!
# Continuous blooming of a given convex polyhedral net

Does every net of a convex polyhedron admit a continuous blooming?
Source: https://en.wikipedia.org/wiki/Blooming_(geometry) (Wikipedia, CC BY-SA 4.0).
Geometric conventions: Demaine et al., *Continuous Blooming of Convex Polyhedra*,
https://doi.org/10.1007/s00373-011-1024-3.
Credit: @Dolcruz

The material points of the cut surface are labelled by a polygonal disk. Its planar
coordinates are just labels: its metric comes from the folded polyhedron. In particular,
two banks of a cut can be distinct material points even when they occupy the same position.
-/

namespace OMA.S_wp_connellys_blooming_conjecture

open Set

abbrev Paper := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

def triangle (v : Fin 3 → Paper) : Set Paper := convexHull ℝ (range v)

/-- A finite piecewise-affine parametrization of the folded surface by a closed disk.
The triangles describe polygonality of the cut pattern; they introduce no hinges. -/
def IsCutDisk (D : Set Paper) (folded : Paper → Space) : Prop :=
  Nonempty (D ≃ₜ Metric.closedBall (0 : Paper) 1) ∧ ContinuousOn folded D ∧
    ∃ cells : Finset (Fin 3 → Paper),
      D = ⋃ v ∈ cells, triangle v ∧
      ∀ v ∈ cells, (interior (triangle v)).Nonempty ∧
        ∃ a : Paper →ᵃ[ℝ] Space, EqOn folded a (triangle v)

/-- Material interiors are embedded. Coincident copies on the boundary account for
closed cut seams on the folded surface and possible boundary contact in a development. -/
def WithoutOverlap (D : Set Paper) (position : Paper → Space) : Prop :=
  ∀ x ∈ interior D, ∀ y ∈ D, position x = position y → x = y

/-- A connected piece of the interior of one original facet, after the cuts, moves
rigidly. Continuity extends this requirement to its edges. Using the material disk
keeps uncut hinges attached without welding together opposite banks of a cut. -/
def RigidOnPlates (P : Set Space) (D : Set Paper) (folded position : Paper → Space) : Prop :=
  ∀ F : Set Space, IsExposed ℝ P F → Module.finrank ℝ (vectorSpan ℝ F) = 2 →
    ∀ U : Set Paper, IsPreconnected U → U ⊆ interior D →
      MapsTo folded U (intrinsicInterior ℝ F) →
      ∀ x ∈ U, ∀ y ∈ U, dist (position x) (position y) = dist (folded x) (folded y)

/-- A particular cut surface and its nonoverlapping planar development. The disk
boundary can cut across a facet, as well as follow an edge of the polyhedron. -/
def IsNet (P : Set Space) (D : Set Paper) (folded flat : Paper → Space) : Prop :=
  IsCutDisk D folded ∧ folded '' D = frontier P ∧ WithoutOverlap D folded ∧
    ContinuousOn flat D ∧ RigidOnPlates P D folded flat ∧ WithoutOverlap D flat ∧
    ∀ x ∈ D, flat x 2 = 0

/-- A continuous motion of this very net, from its folded placement to its specified
planar placement. Time runs over the closed unit interval. -/
def HasBlooming (P : Set Space) (D : Set Paper) (folded flat : Paper → Space) : Prop :=
  ∃ motion : ℝ → Paper → Space,
    ContinuousOn (fun z : ℝ × Paper => motion z.1 z.2) (Icc 0 1 ×ˢ D) ∧
    EqOn (motion 0) folded D ∧ EqOn (motion 1) flat D ∧
    ∀ t ∈ Icc (0 : ℝ) 1, RigidOnPlates P D folded (motion t) ∧ WithoutOverlap D (motion t)

theorem main :
    ∀ vertices : Finset Space, let P := convexHull ℝ (vertices : Set Space)
      (interior P).Nonempty → ∀ (D : Set Paper) (folded flat : Paper → Space),
        IsNet P D folded flat → HasBlooming P D folded flat := by
  sorry

end OMA.S_wp_connellys_blooming_conjecture
