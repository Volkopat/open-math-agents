import Mathlib

/-!
# Extending a line arrangement to triangulate its bounded cells

Every finite arrangement of lines in the real plane can be extended to a finite
arrangement whose bounded complementary components are open triangles.

[MathOverflow question](https://mathoverflow.net/questions/155196)
-/

namespace OMA.S_mo_155196

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsLine (L : AffineSubspace ℝ Plane) : Prop :=
  (L : Set Plane).Nonempty ∧ Module.finrank ℝ L.direction = 1

def Complement (lines : Set (AffineSubspace ℝ Plane)) : Set Plane :=
  (⋃ L ∈ lines, (L : Set Plane))ᶜ

theorem main :
    ∀ lines : Set (AffineSubspace ℝ Plane),
      lines.Finite → (∀ L ∈ lines, IsLine L) →
      ∃ extended : Set (AffineSubspace ℝ Plane),
        extended.Finite ∧ lines ⊆ extended ∧ (∀ L ∈ extended, IsLine L) ∧
        ∀ x ∈ Complement extended,
          Bornology.IsBounded (connectedComponentIn (Complement extended) x) →
          ∃ v : Fin 3 → Plane, AffineIndependent ℝ v ∧
            connectedComponentIn (Complement extended) x =
              interior (convexHull ℝ (Set.range v)) := by
  sorry

end OMA.S_mo_155196
