import OMAStatements.S_oeis_a025754

theorem OMA.solution : type_of% @OMA.S_oeis_a025754.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  have hsub : m + 1 - m = 1 := by omega
  have h := Ring.choose_smul_choose (1 / 9 : ℚ) (n := m + 1) (k := m) (by omega)
  simp only [Nat.choose_succ_self_right, hsub, Ring.choose_one_right, nsmul_eq_mul] at h
  simp only [Nat.add_sub_cancel, S_oeis_a025754.a, hm, Nat.succ_ne_zero, if_false, pow_succ]
  push_cast at h ⊢
  linear_combination (9 * (-81 : ℚ) ^ m) * h
