import OMAStatements.S_oeis_a025754

theorem OMA.solution : type_of% @OMA.S_oeis_a025754.main := by
  rintro (_ | m) hn
  · omega
  have h := Ring.choose_smul_choose (1 / 9 : ℚ) (n := m + 1) (k := m) (by omega)
  simp only [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega, Ring.choose_one_right,
    nsmul_eq_mul] at h
  simp only [Nat.add_sub_cancel, S_oeis_a025754.a, show m ≠ 0 by omega, if_false, pow_succ]
  push_cast at h ⊢
  linear_combination 9 * (-81 : ℚ) ^ m * h
