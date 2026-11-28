import Mathlib

/-!
# A conjecture on six planes

Source: https://mathoverflow.net/questions/234762
Conjecture (asker, checked numerically): let `P₁, P₂, P₃, P₄` be four points of a plane `σ` in
space, and for each pair `i < j` let `σᵢⱼ` be a plane through `Pᵢ` and `Pⱼ`. Let `Pᵢⱼₖ` be the
common point of `σᵢⱼ, σⱼₖ, σₖᵢ`. Then `P₁₂₃, P₁₂₄, P₁₃₄, P₂₃₄` lie on a plane.

Conventions. Space is `ℝ³`, planes are affine subspaces with two-dimensional direction. The
`Pᵢ` are distinct, and every `σᵢⱼ` differs from `σ`. "The common point" is read as: the
three planes meet in exactly one point, `Pᵢⱼₖ`. The family `S` of planes is indexed symmetrically
(`S i j = S j i`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_234762

theorem main :
    ∀ (P : Fin 4 → EuclideanSpace ℝ (Fin 3)) (σ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
      (S : Fin 4 → Fin 4 → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
      (Q : Fin 4 → Fin 4 → Fin 4 → EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ σ.direction = 2 → (∀ i, P i ∈ σ) → Function.Injective P →
      (∀ i j, S i j = S j i) →
      (∀ i j, i ≠ j → Module.finrank ℝ (S i j).direction = 2 ∧ P i ∈ S i j ∧ P j ∈ S i j ∧
        S i j ≠ σ) →
      (∀ i j k, i < j → j < k →
        ((S i j : Set (EuclideanSpace ℝ (Fin 3))) ∩ S j k ∩ S i k = {Q i j k})) →
      Coplanar ℝ ({Q 0 1 2, Q 0 1 3, Q 0 2 3, Q 1 2 3} : Set (EuclideanSpace ℝ (Fin 3))) := by
  sorry

end OMA.S_mo_234762
