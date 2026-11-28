import Mathlib

/-!
# Positivity of a Hankel matrix of Bernoulli polynomials

Source: Jean-François Coulombel, https://mathoverflow.net/questions/504555 (CC BY-SA 4.0).
Credit: @connoranderson.

The source asks for positive definiteness at m = 2d+1 and also asks whether
m = d+1 suffices. The matrix is positive definite for all m ≥ d+1.
-/

namespace OMA.S_mo_504555

open Polynomial

noncomputable def momentPoly (k : ℕ) : ℝ[X] :=
  C ((k+1 : ℝ)⁻¹) * (Polynomial.bernoulli (k+1)).map (algebraMap ℚ ℝ)

noncomputable def hankel (d m : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  fun i j => (momentPoly (i.val+j.val)).eval (m : ℝ)

theorem main : ∀ d m : ℕ, d+1 ≤ m → (hankel d m).PosDef := by
  sorry

end OMA.S_mo_504555
