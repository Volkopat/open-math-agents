import Mathlib

/-!
# Uniform integral linear formulas for making a symmetric matrix positive definite

Source: Hvjurthuk, https://mathoverflow.net/questions/428655 (CC BY-SA 4.0).
Contribution by @connoranderson.

The proposed divisibility requirement already fails for a singular matrix with
a negative eigenvalue. Even on invertible mixed-sign inputs of size two, no
fixed affine integral formula of any output dimension works universally. A
uniform quadratic formula does work on every nonsingular input.
-/
namespace OMA.S_mo_428655
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ
def realify {n : ℕ} (A : Mat n) : Matrix (Fin n) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
def hasNegative {n : ℕ} (A : Mat n) : Prop := ∃ t : ℝ, t<0 ∧
  ∃ v : Fin n → ℝ, v≠0 ∧ realify A *ᵥ v=t • v
def works {n m : ℕ} (A : Mat n) (B : Mat m) : Prop :=
  (realify B).PosDef ∧ A.det ∣ B.det

theorem main :
    (∃ A : Mat 2, A.IsSymm ∧ hasNegative A ∧ A.det=0 ∧ ∀ (m : ℕ) (B : Mat m),¬ works A B) ∧
    (∀ (m : ℕ) (C : Mat m) (L : Mat 2 →ₗ[ℤ] Mat m),
      ∃ A : Mat 2, A.IsSymm ∧ hasNegative A ∧ hasNegative (-A) ∧ A.det≠0 ∧ ¬ works A (C+L A)) ∧
    (∀ (n : ℕ) (A : Mat n), A.det≠0 → works A (Aᵀ*A) ∧ (Aᵀ*A).det=A.det^2) := by sorry
end OMA.S_mo_428655
