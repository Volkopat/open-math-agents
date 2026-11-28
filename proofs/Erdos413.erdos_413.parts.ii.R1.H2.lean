import OMAReductions.R_Erdos413_erdos_413_parts_ii_R1

theorem OMA.solution : OMA.R_Erdos413_erdos_413_parts_ii_R1.H2 := fun C h =>
  ⟨C⁻¹, by positivity, fun k _ => by field_simp; exact Real.log_le_sub_one_of_pos (by norm_cast; omega)⟩
