import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

namespace OMA.S_mo_149286

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A solid convex polyhedron is the convex hull of finitely many points and
has nonempty interior in three-space. -/
def IsConvexPolyhedron (P : Set Space) : Prop :=
  (interior P).Nonempty ∧ ∃ vertices : Finset Space, P = convexHull ℝ (vertices : Set Space)

/-- The faces ordered by inclusion. Every face of a convex polytope is exposed. -/
abbrev FaceOrder (P : Set Space) := {F : Set Space // IsExposed ℝ P F}

/-- A combinatorially equivalent realization with rational multiples of pi
for the angles between incident edges. -/
theorem main :
    ∀ P : Set Space, IsConvexPolyhedron P →
      ∃ Q : Set Space, IsConvexPolyhedron Q ∧
        Nonempty (FaceOrder P ≃o FaceOrder Q) ∧
          ∀ v a b : Space, a ≠ v → b ≠ v → a ≠ b →
            IsExposed ℝ Q (segment ℝ v a) → IsExposed ℝ Q (segment ℝ v b) →
              ∃ q : ℚ, InnerProductGeometry.angle (a - v) (b - v) = (q : ℝ) * Real.pi := by
  sorry

end OMA.S_mo_149286
