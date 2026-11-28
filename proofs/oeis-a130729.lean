import OMAStatements.S_oeis_a130729
theorem OMA.solution : type_of% @OMA.S_oeis_a130729.main := by
  rintro n ⟨k, rfl⟩
  have h : 2 ^ (2 * k + 1) % 3 = 2 := by simp [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  have : 2 ^ 2 ^ (2 * k + 1) % 7 = 4 := by
    rw [← Nat.div_add_mod (2 ^ (2 * k + 1)) 3, h, pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  unfold OMA.S_oeis_a130729.a
  omega
