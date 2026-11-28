import Mathlib

/-!
# Maximizing the matrix norm

Source: https://mathoverflow.net/questions/57550 (Danny Kane, CC BY-SA 2.5).
Credit: @connoranderson

The matrix two-norm is the induced Euclidean norm. A rotation has determinant one.
Entrywise, blockProduct is exactly the product of the three matrices in the question.
The theorem gives an attained dual formula and a recovery test for a maximizing rotation.
For a finite approximation, maximize a 3 by 3 nuclear norm over two finite unit-ball nets,
then maximize the corresponding absolute trace by an orthogonal Procrustes step.
-/

namespace OMA.S_mo_57550
open Matrix
abbrev Three := Matrix (Fin 3) (Fin 3) ℝ
def rotation (R : Three) : Prop := Rᵀ*R=1 ∧ R.det=1
noncomputable def nuclear (C : Three) : ℝ := ∑ i : Fin 3,C.toEuclideanLin.singularValues i.val
noncomputable def blockProduct {m n : ℕ} (A : Matrix (Fin m) (Fin n × Fin 3) ℝ)
    (v : Fin n → Fin 3 → ℝ) (R : Three) : Matrix (Fin m) (Fin n) ℝ :=
  .of fun t j => ∑ a,A t (j,a)*(∑ b,R a b*v j b)
noncomputable def coefficient {m n : ℕ} (A : Matrix (Fin m) (Fin n × Fin 3) ℝ)
    (v : Fin n → Fin 3 → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) : Three :=
  .of fun a b => ∑ t,∑ j,y t*x j*A t (j,a)*v j b
noncomputable def objective {m n : ℕ} (A : Matrix (Fin m) (Fin n × Fin 3) ℝ)
    (v : Fin n → Fin 3 → ℝ) (R : Three) : ℝ :=
  ‖(blockProduct A v R).toEuclideanLin.toContinuousLinearMap‖
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
def unitNet {d : ℕ} (δ : ℝ) (X : Finset (Vec d)) : Prop :=
  (∀ u ∈ X, ‖u‖ ≤ 1) ∧ ∀ x : Vec d, ‖x‖ ≤ 1 → ∃ u ∈ X, ‖x-u‖ ≤ δ

theorem main :
    (∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ X : Finset (Vec d), unitNet δ X) ∧
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n × Fin 3) ℝ) (v : Fin n → Fin 3 → ℝ),
      ∃ R : Three, rotation R ∧ (∀ S, rotation S → objective A v S ≤ objective A v R) ∧
        (∃ x : Vec n, ∃ y : Vec m, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
          nuclear (coefficient A v x y) = objective A v R) ∧
        (∀ (x : Vec n) (y : Vec m), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          nuclear (coefficient A v x y) ≤ objective A v R ∧
          ∃ S, rotation S ∧ |(Sᵀ * coefficient A v x y).trace| = nuclear (coefficient A v x y) ∧
            nuclear (coefficient A v x y) ≤ objective A v S) ∧
        (∀ (δ : ℝ) (X : Finset (Vec n)) (Y : Finset (Vec m)), unitNet δ X → unitNet δ Y →
          ∃ x ∈ X, ∃ y ∈ Y, (1 - 2*δ) * objective A v R ≤ nuclear (coefficient A v x y)) := by
  sorry
end OMA.S_mo_57550
