import Mathlib

/-!
# Generalised Empty Hexagon Conjecture

Source: https://www.openproblemgarden.org/op/generalised_empty_hexagon_conjecture
(D. Wood)
Credit: @ishaanzee

**Conjecture.** For each `ℓ ≥ 3` there is an integer `f(ℓ)` such that every set of at least `f(ℓ)`
points in the plane contains `ℓ` collinear points or an empty hexagon.

Here an empty hexagon in a set of points `P` consists of a subset `S ⊆ P` of six points in convex
position with no other point in `P` in the convex hull of `S`. (The case `ℓ = 3`, point sets in
general position, is the theorem of Gerken and Nicolás.)

Formalization: the plane is `EuclideanSpace ℝ (Fin 2)` and point sets are finite sets. `ℓ`
collinear points are an `ℓ`-element subset that is `Collinear`. Six points are in convex position
when none of them lies in the convex hull of the other five.
-/

namespace OMA.S_opg_generalised_empty_hexagon_conjecture

/-- `S ⊆ P` is an empty hexagon of `P`: six points in convex position whose convex hull contains no
other point of `P`. -/
def IsEmptyHexagon (P S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  S ⊆ P ∧ S.card = 6 ∧
    (∀ x ∈ S, x ∉ convexHull ℝ ((S.erase x : Finset _) : Set (EuclideanSpace ℝ (Fin 2)))) ∧
    ∀ p ∈ P, p ∉ S → p ∉ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/-- **Generalised empty hexagon conjecture.** -/
theorem main : ∀ ℓ : ℕ, 3 ≤ ℓ → ∃ f : ℕ, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), f ≤ P.card →
    (∃ L ⊆ P, L.card = ℓ ∧ Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2)))) ∨
      ∃ S, IsEmptyHexagon P S := by
  sorry

end OMA.S_opg_generalised_empty_hexagon_conjecture
