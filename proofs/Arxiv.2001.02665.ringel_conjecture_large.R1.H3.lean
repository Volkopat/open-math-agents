import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1

/-! The factorial formula for choosing two reduces to division by two. -/

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3 := by
  intro n
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_left_comm,
    Nat.mul_div_cancel_left _ (by decide)]
