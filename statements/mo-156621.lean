import Mathlib

namespace OMA.S_mo_156621

/-- A simple C-star algebra has only the two trivial closed two-sided ideals. -/
def IsSimple (A : Type) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ I : Submodule ℂ A, IsClosed (I : Set A) →
    (∀ a x : A, x ∈ I → a * x ∈ I ∧ x * a ∈ I) →
    I = ⊥ ∨ I = ⊤

/-- Are the underlying Banach spaces of all simple separable
infinite-dimensional complex C-star algebras isomorphic? -/
theorem main :
    ∀ (A B : Type) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
      [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B],
      IsSimple A → IsSimple B →
        ¬ FiniteDimensional ℂ A → ¬ FiniteDimensional ℂ B →
          Nonempty (A ≃L[ℂ] B) := by
  sorry

end OMA.S_mo_156621
