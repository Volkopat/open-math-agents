import Mathlib

/-!
# Zero-energy multiplicity for finitely many local point interactions in three dimensions

Source: https://mathoverflow.net/questions/498100
Question by Raffaele Scandone (CC BY-SA 4.0).
Credit: @city-ships

Scandone asks for the maximum possible dimension of the zero-sum part of the
kernel, allowing the number of distinct sites, their positions, and their real
couplings to vary. The proposed answer is that these dimensions are unbounded.
-/

namespace OMA.S_mo_498100

abbrev Position := EuclideanSpace ℝ (Fin 3)

noncomputable def interaction {N : ℕ} (y : Fin N → Position) (α : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if i = j then α i else (dist (y i) (y j))⁻¹

/-- The kernel vectors whose coefficients add to zero. -/
noncomputable def modes {N : ℕ} (y : Fin N → Position) (α : Fin N → ℝ) :
    Submodule ℝ (Fin N → ℝ) where
  carrier := {v | (interaction y α).mulVec v = 0 ∧ ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    exact ⟨by rw [Matrix.mulVec_add, hu.1, hv.1, add_zero],
      by simp only [Pi.add_apply, Finset.sum_add_distrib, hu.2, hv.2, add_zero]⟩
  smul_mem' := by
    intro c v hv
    exact ⟨by rw [Matrix.mulVec_smul, hv.1, smul_zero],
      by simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv.2, mul_zero]⟩

theorem main :
    ∀ M : ℕ, ∃ (N : ℕ) (y : Fin N → Position) (α : Fin N → ℝ),
      2 ≤ N ∧ Function.Injective y ∧ M ≤ Module.finrank ℝ (modes y α) := by
  sorry

end OMA.S_mo_498100
