import Mathlib

/-!
# A lower bound for the sliced distance between positive semidefinite matrices

Source: Lénaïc Chizat, https://mathoverflow.net/questions/353710 (CC BY-SA 4.0).
Credit: @connoranderson.

The sphere law is a probability measure supported on unit vectors and invariant
under all orthogonal transformations. The bound is written without division so
it includes zero matrices. Its numerator for C = A - B is the squared trace
plus twice the squared Frobenius norm. Scalar matrices attain the bound.
-/

namespace OMA.S_mo_353710
open MeasureTheory

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def IsUniform {d : ℕ} (μ : Measure (E d)) : Prop :=
  (∀ᵐ x ∂μ, ‖x‖=1) ∧ ∀ e : E d ≃ₗᵢ[ℝ] E d, MeasurePreserving e μ μ

noncomputable def q {d : ℕ} (A : Mat d) (x : E d) : ℝ := inner ℝ x (A.toEuclideanLin x)

noncomputable def op {d : ℕ} (A : Mat d) : ℝ := ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=Fin d) A‖

noncomputable def squared {d : ℕ} (μ : Measure (E d)) (A B : Mat d) : ℝ :=
  ∫ x, (Real.sqrt (q A x) - Real.sqrt (q B x))^2 ∂μ

theorem main : ∀ {d : ℕ}, 0 < d → ∀ (μ : Measure (E d)) [IsProbabilityMeasure μ],
    IsUniform μ →
    (∀ (A B : Mat d), A.PosSemidef → B.PosSemidef →
      (A-B).trace^2 + 2*((A-B)*(A-B)).trace ≤
        (d:ℝ)*((d:ℝ)+2)*(Real.sqrt (op A)+Real.sqrt (op B))^2*squared μ A B) ∧
    (∀ (A B : Mat d), A.PosSemidef → B.PosSemidef → (squared μ A B=0 ↔ A=B)) ∧
    (∀ a b : ℝ, 0≤a → 0≤b → squared μ (a • (1:Mat d)) (b • (1:Mat d)) =
      (Real.sqrt a - Real.sqrt b)^2) := by
  sorry

end OMA.S_mo_353710
