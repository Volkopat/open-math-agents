import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Positive eigenvalue of a diagonally perturbed stochastic matrix

Source: https://mathoverflow.net/questions/124716
Credit: @MMexicann
-/

open scoped BigOperators

namespace OMA.S_mo_124716

theorem main :
    ∀ (n : ℕ) (a : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (k : ℝ),
    Monotone a → (∃ i, 0 < a i) →
    (∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) →
    (∀ i, ∑ j, P i j = 1) →
    (∀ i j, ∃ m : ℕ, 0 < (P ^ m) i j) →
    (∀ z : ℂ, (P.map fun x : ℝ => (x : ℂ)).charpoly.eval z = 0 → z.im = 0) →
    0 < k →
    ∃ z : ℝ, 0 < z ∧ (Matrix.diagonal a + k • P).charpoly.eval z = 0 := by
  sorry

end OMA.S_mo_124716
