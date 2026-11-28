import Mathlib

/-!
# Monotonicity of the Gaussian kernel log determinant

Source: Heinrich A, https://mathoverflow.net/questions/395730 (CC BY-SA 4.0).
Credit: @connoranderson.

The input locations are distinct points of the real line, the amplitude
is positive, and the lengthscale ranges over the positive reals.
-/

namespace OMA.S_mo_395730

noncomputable def gaussian {n : ℕ} (x : Fin n → ℝ) (σ θ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => σ * Real.exp (-(x i - x j)^2/(2*θ^2)))

theorem main :
    ∀ (n : ℕ) (x : Fin n → ℝ), Function.Injective x → ∀ σ : ℝ, 0<σ →
      (∀ θ : ℝ, 0<θ → DifferentiableAt ℝ (fun s => Real.log (gaussian x σ s).det) θ ∧
        deriv (fun s => Real.log (gaussian x σ s).det) θ ≤ 0) ∧
      AntitoneOn (fun s => Real.log (gaussian x σ s).det) (Set.Ioi 0) := by
  sorry

end OMA.S_mo_395730
