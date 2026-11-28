import OMAReductions.R_LebesgueNagell_lebesgue_nagell_R1

/-!
# Proof of `LebesgueNagell.lebesgue_nagell.R1.H2`

For any odd natural number `p`, `(-1 : ℤ) ^ p = -1`, while `1 ^ 2 - 2 = -1` and `(-1) ^ 2 - 2 = -1`.
-/

theorem OMA.solution : OMA.R_LebesgueNagell_lebesgue_nagell_R1.H2 := by
  intro p _ hodd x y ⟨hx, hy⟩
  subst hy
  rw [hodd.neg_one_pow]
  rcases hx with rfl | rfl <;> norm_num
