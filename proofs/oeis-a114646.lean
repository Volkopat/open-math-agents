import OMAStatements.S_oeis_a114646

open OMA.S_oeis_a114646 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a114646.main) := by
  rintro ⟨-, h1, h2, h3⟩
  have h := h3 3 le_rfl
  rw [a, Matrix.inv_eq_right_inv (B := !![2, -1, 0; -1, 2, -1; 0, -1, 1]) (by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [M, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two])] at h
  norm_num [h1, h2, pow_succ, Matrix.mul_fin_three, Matrix.trace_fin_three, Matrix.cons_val_two] at h
