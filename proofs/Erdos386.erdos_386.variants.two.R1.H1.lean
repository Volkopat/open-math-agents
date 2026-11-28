import OMAReductions.R_Erdos386_erdos_386_variants_two_R1

theorem OMA.solution : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := by
  rintro P hP ⟨k, hk⟩
  obtain ⟨t, rfl⟩ := (Nat.odd_mul.mp (hk ▸ (⟨4 * P, by omega⟩ : Odd (8 * P + 1)))).1
  have h : (t + 1) * t = P * 2 := by nlinarith
  refine ⟨t + 1, by nlinarith, ?_, by nlinarith⟩
  rw [Nat.choose_two_right, Nat.add_sub_cancel, h]
  omega
