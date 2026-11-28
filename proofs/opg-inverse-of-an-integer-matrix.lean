import OMAStatements.S_opg_inverse_of_an_integer_matrix

-- Reuses the existing two-row parity counterexample.
open OMA.S_opg_inverse_of_an_integer_matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_inverse_of_an_integer_matrix.main) := by
  intro h
  have key := h 2 2 le_rfl (fun _ => 2) !![1, 0; 1, 0] (fun _ => le_rfl)
  have hp : primitiveRows (fun _ : Fin 2 => 2) !![1, 0; 1, 0] := by
    intro i q hq
    fin_cases i <;> simpa [block] using hq (Sum.inr 0)
  obtain ⟨R, hR⟩ := key.mpr hp
  have h₀ := congrFun (congrFun hR 0) 0
  have h₁ := congrFun (congrFun hR 1) 0
  simp [block, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.diagonal_apply] at h₀ h₁
  omega
