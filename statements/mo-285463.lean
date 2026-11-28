import Mathlib

/-!
# Uniqueness of tensor-product inner products

Source: Manish Kumar, https://mathoverflow.net/questions/285463 (CC BY-SA 3.0).
Credit: @connoranderson.

The question permits inner-product spaces and does not specify the scalar
field. Complex sesquilinear forms are determined by their values on the
diagonals of simple tensors. Over the reals a positive definite counterexample
already exists on ℝ² ⊗ ℝ², written in its usual four product-basis coordinates.
-/

namespace OMA.S_mo_285463

open Matrix
open scoped TensorProduct

def coords (x y : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![x 0*y 0, x 0*y 1, x 1*y 0, x 1*y 1]

theorem main :
    (∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      (B : (H ⊗[ℂ] K) →ₗ⋆[ℂ] (H ⊗[ℂ] K) →ₗ[ℂ] ℂ),
      (∀ h k, B (h ⊗ₜ[ℂ] k) (h ⊗ₜ[ℂ] k) = inner ℂ h h * inner ℂ k k) →
      B = innerₛₗ ℂ) ∧
    (∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.PosDef ∧ A ≠ 1 ∧
      ∀ x y : Fin 2 → ℝ, (coords x y) ⬝ᵥ (A *ᵥ coords x y) =
        (∑ i, (x i)^2)*(∑ i, (y i)^2)) := by
  sorry

end OMA.S_mo_285463
