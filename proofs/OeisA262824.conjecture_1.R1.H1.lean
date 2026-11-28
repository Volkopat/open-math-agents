import OMAReductions.R_OeisA262824_conjecture_1_R1

theorem OMA.solution : OMA.R_OeisA262824_conjecture_1_R1.H1 := by
  intro s q hq hpf
  obtain ⟨a, b, rfl⟩ := Nat.eq_sq_add_sq_iff.mpr hpf
  clear hpf
  wlog h : a ≤ b generalizing a b
  · rw [add_comm (a ^ 2)]; exact this b a (by linarith) (by omega)
  have : a ≤ s ^ 2 := by nlinarith
  refine ⟨6 * s * b, 2 * s ^ 2 - 2 * a, 2 * s ^ 2 + a, a, ?_⟩
  zify [(by omega : 2 * a ≤ 2 * s ^ 2)]
  ring
