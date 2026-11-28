import OMAStatements.S_mo_254890
import Mathlib

open OMA.S_mo_254890

open scoped Matrix.Norms.L2Operator in
theorem OMA.solution : type_of% @OMA.S_mo_254890.main := by
  intro n L M _ ⟨h1, h2, _, _⟩ hT
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := FiniteDimensional.complete ℝ _
  set U := Units.oneSub (1 - L) hT with hUdef
  have hU : (U : Matrix (Fin n) (Fin n) ℝ) = L := by
    rw [hUdef, Units.val_oneSub]; abel
  have e1 : (↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) * L = 1 := by rw [← hU]; exact U.inv_mul
  have e2 : L * (↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = 1 := by rw [← hU]; exact U.mul_inv
  have hM : M = ↑U⁻¹ := by
    calc M = (↑U⁻¹ * L) * M * (L * ↑U⁻¹) := by rw [e1, e2, one_mul, mul_one]
      _ = ↑U⁻¹ * (L * M * L) * ↑U⁻¹ := by noncomm_ring
      _ = ↑U⁻¹ := by rw [h1, e1, one_mul]
  have hinv : (↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = ∑' k : ℕ, (1 - L) ^ k := rfl
  have hb := tsum_geometric_le_of_norm_lt_one (1 - L) hT
  have h1le : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
    rcases n with _ | m
    · rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) ℝ) 0, norm_zero]; norm_num
    · rw [norm_one]
  rw [hM, hinv, one_div]
  linarith
