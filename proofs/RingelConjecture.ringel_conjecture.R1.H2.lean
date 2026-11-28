import OMAReductions.R_RingelConjecture_ringel_conjecture_R1

/-! `C(2n+1, 2) = (2n+1)(2n)/2 = (2n+1)n`. -/

theorem OMA.solution : OMA.R_RingelConjecture_ringel_conjecture_R1.H2 := by
  intro n
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm 2 n, ← mul_assoc,
    Nat.mul_div_cancel _ (by norm_num)]
