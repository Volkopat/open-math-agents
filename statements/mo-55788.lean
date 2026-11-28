import Mathlib

/-!
# Simply connected plane sections of a two-convex domain

The question asks whether each component of every affine two-plane section of
an open simply connected two-convex subset of Euclidean space is simply connected.

[MathOverflow question](https://mathoverflow.net/questions/55788/two-convexity-%E2%87%92-lefschetz)
-/

namespace OMA.S_mo_55788

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def IsTwoConvex {d : ℕ} (region : Set (Ambient d)) : Prop :=
  ∀ (v : Fin 4 → Ambient d) (omitted : Fin 4), AffineIndependent ℝ v →
    (∀ i : Fin 4, i ≠ omitted →
      convexHull ℝ (v '' {j : Fin 4 | j ≠ i}) ⊆ region) →
    convexHull ℝ (Set.range v) ⊆ region

theorem main :
    ∀ (d : ℕ) (region : Set (Ambient d)),
      IsOpen region → SimplyConnectedSpace region → IsTwoConvex region →
      ∀ P : AffineSubspace ℝ (Ambient d),
        (P : Set (Ambient d)).Nonempty → Module.finrank ℝ P.direction = 2 →
        ∀ x ∈ region ∩ (P : Set (Ambient d)),
          SimplyConnectedSpace (connectedComponentIn (region ∩ (P : Set (Ambient d))) x) := by
  sorry

end OMA.S_mo_55788
