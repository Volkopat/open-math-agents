import OMAStatements.S_mo_445970
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_445970.main) := by
  intro h
  obtain ⟨U, -, hU⟩ := h 1 2 (fun _ => !![0, 1; 0, 0]) (fun _ => !![1, 0; 0, 0]) fun x => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have := congrFun (congrFun (hU 0) 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this
