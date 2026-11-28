import FormalConjectures.Wikipedia.InscribedSquare
import Mathlib

/-!
# The smooth rectangular peg problem

Use the Greene–Lobb rotated-chord intersection and the unit rotation
corresponding to the prescribed side ratio. The algebraic conversion
checks the exact diagonal and side conditions of the upstream rectangle.

Source: Greene and Lobb, arXiv:2005.09193.
Credit: @justusklocke-cloud
-/

namespace OMA.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R1

open Topology ContDiff Manifold InscribedSquare
open scoped EuclideanGeometry

theorem rectangle_from_rotated_diagonals (e : ℝ² ≃ₗᵢ[ℝ] ℂ) {a b c d : ℝ²} {ζ : ℂ} {r : ℝ}
    (hNorm : ‖ζ‖ = 1) (hMinus : 1 - ζ ≠ 0) (hPlus : 1 + ζ ≠ 0)
    (hRatio : ‖1 - ζ‖ = r * ‖1 + ζ‖)
    (hMid : e a + e c = e b + e d) (hRot : e b - e d = ζ * (e a - e c))
    (hDiag : e a - e c ≠ 0) : IsRectangle a b c d r := by
  have hAB : e a - e b = ((1 - ζ) * (e a - e c)) / 2 := by
    apply (eq_div_iff (show (2 : ℂ) ≠ 0 by norm_num)).mpr
    calc
      _ = (e a - e c) - (e b - e d) := by linear_combination hMid
      _ = _ := by rw [hRot]; ring
  have hBC : e b - e c = ((1 + ζ) * (e a - e c)) / 2 := by
    apply (eq_div_iff (show (2 : ℂ) ≠ 0 by norm_num)).mpr
    calc
      _ = (e a - e c) + (e b - e d) := by linear_combination -hMid
      _ = _ := by rw [hRot]; ring
  have hnAB : e a - e b ≠ 0 := by
    rw [hAB]
    exact div_ne_zero (mul_ne_zero hMinus hDiag) (by norm_num)
  have hnBC : e b - e c ≠ 0 := by
    rw [hBC]
    exact div_ne_zero (mul_ne_zero hPlus hDiag) (by norm_num)
  have hab : a ≠ b := fun h => hnAB (by rw [h,sub_self])
  have hbc : b ≠ c := fun h => hnBC (by rw [h,sub_self])
  have hd (p q : ℝ²) : dist p q = ‖e p - e q‖ := by
    rw [← e.isometry.dist_eq p q,dist_eq_norm]
  refine ⟨e.injective (by simpa only [map_add] using hMid),?_,hab,hbc,?_⟩
  · rw [hd a c, hd b d, hRot, norm_mul, hNorm, one_mul]
  · apply (div_eq_iff (dist_ne_zero.mpr hbc)).mpr
    have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hd a b, hd b c, hAB, hBC, norm_div, norm_div, norm_mul, norm_mul, hTwo,hRatio]
    ring

/-- The Greene–Lobb intersection away from the diagonal of the chord tori. -/
def H1 : Prop :=
  ∀ (γ : Circle → ℝ²), IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ →
    ∀ ζ : ℂ, ‖ζ‖ = 1 → 1 - ζ ≠ 0 → 1 + ζ ≠ 0 →
      let e := Complex.orthonormalBasisOneI.repr.symm
      ∃ a b c d : Circle, e (γ a) + e (γ c) = e (γ b) + e (γ d) ∧
        e (γ b) - e (γ d) = ζ * (e (γ a) - e (γ c)) ∧
        e (γ a) - e (γ c) ≠ 0

/-- Prescribe the side ratio by a unit rotation. -/
def H2 : Prop :=
  ∀ r : ℝ, 0 < r → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ 1 - ζ ≠ 0 ∧ 1 + ζ ≠ 0 ∧
    ‖1 - ζ‖ = r * ‖1 + ζ‖

theorem main : H1 → H2 → type_of% @InscribedSquare.exists_inscribed_rectangle_of_smooth := by
  intro hIntersection hRotation γ hγ r hr
  obtain ⟨ζ,hNorm,hMinus,hPlus,hRatio⟩ := hRotation r hr
  obtain ⟨a,b,c,d,hMid,hRot,hDiag⟩ := hIntersection γ hγ ζ hNorm hMinus hPlus
  exact ⟨a,b,c,d,rectangle_from_rotated_diagonals
    Complex.orthonormalBasisOneI.repr.symm hNorm hMinus hPlus hRatio hMid hRot hDiag⟩

end OMA.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R1
