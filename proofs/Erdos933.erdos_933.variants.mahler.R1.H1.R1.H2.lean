import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1

-- Shortens the spanning argument in @JamesSlash's merged proof #11047.
theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1.H2 := by
  intro W hW
  apply Set.Subsingleton.finite
  intro n hn m hm
  by_contra h
  have hd : (m : ℚ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm h)
  apply hW
  rw [eq_top_iff]
  rintro ⟨x,y⟩ _
  let a : ℚ := (x - (y-x)*n) / ((m : ℚ)-n)
  convert W.add_mem (W.smul_mem a hm) (W.smul_mem (y-x-a) hn) using 1
  ext <;> dsimp [a] <;> field_simp [hd] <;> ring
