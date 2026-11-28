import Mathlib

namespace OMA.S_mo_223642

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def IsFaceVertexSet {d : ℕ} (P : Set (Space d))
    (s : Set (P.extremePoints ℝ)) : Prop :=
  ∃ F : Set (Space d), IsExposed ℝ P F ∧ s = Subtype.val ⁻¹' F

/-- Does every combinatorial automorphism of an origin-symmetric convex
polytope send each pair of opposite vertices to a pair of opposite vertices? -/
theorem main :
    ∀ (d : ℕ) (P : Set (Space d)),
      (∃ S : Finset (Space d), S.Nonempty ∧ P = convexHull ℝ (S : Set (Space d))) →
      (∀ x ∈ P, -x ∈ P) →
      ∀ f : (P.extremePoints ℝ) ≃ (P.extremePoints ℝ),
        (∀ s, IsFaceVertexSet P s ↔ IsFaceVertexSet P (f '' s)) →
        ∀ x y : P.extremePoints ℝ, y.val = -x.val → (f y).val = -(f x).val := by
  sorry

end OMA.S_mo_223642
