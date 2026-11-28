import Mathlib

namespace OMA.S_mo_379560

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Time := Set.Icc (0 : ℝ) 1

/-- The six closed edge segments of a tetrahedron with vertices v. -/
def bars (v : Fin 4 → Space) : Set Space :=
  {x | ∃ i j, i ≠ j ∧ x ∈ segment ℝ (v i) (v j)}

/-- A continuous motion of the ambient Euclidean space starting at the identity. -/
def IsRigidMotion (F : C(Time × Space, Space)) : Prop :=
  (∀ t : Time, (t : ℝ) = 0 → ∀ x : Space, F (t, x) = x) ∧
    ∀ t : Time, Isometry (fun x : Space => F (t, x)) ∧
      Function.Surjective (fun x : Space => F (t, x))

/-- Every three-dimensional convex body can be trapped by the edge cage
of a tetrahedron. -/
theorem main :
    ∀ K : Set Space, Convex ℝ K → IsCompact K → (interior K).Nonempty →
      ∃ v : Fin 4 → Space, AffineIndependent ℝ v ∧
        Disjoint (bars v) (interior K) ∧
          ∀ F : C(Time × Space, Space), IsRigidMotion F →
            (∀ t : Time,
              (((fun x : Space => F (t, x)) '' K) ∩ convexHull ℝ (Set.range v)).Nonempty) ∨
            (∃ t : Time, (bars v ∩ interior ((fun x : Space => F (t, x)) '' K)).Nonempty) := by
  sorry

end OMA.S_mo_379560
