import OMAStatements.S_oeis_a273871

theorem OMA.solution : type_of% @OMA.S_oeis_a273871.main := by
  refine ⟨fun p => ⟨fun ⟨hp, hd⟩ => ⟨hp, fun k => ?_⟩, fun ⟨hp, h⟩ => ⟨hp, by simpa using h 1⟩⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact hd.trans (by simpa using Nat.sub_dvd_pow_sub_pow (4 ^ (p - 1)) 1 k)
  · intro m hm
    refine ⟨hm, ?_⟩
    have hF : Nat.fermatNumber m - 1 = 2 ^ 2 ^ m := by simp [Nat.fermatNumber]
    rw [hF]
    have hN : (2 ^ 2 ^ m) ^ 2 + 1 = 2 ^ 2 ^ (m + 1) + 1 := by
      rw [← pow_mul, pow_succ]
    rw [hN]
    set e := 2 ^ (m + 1) with he
    have h1 : 2 ^ e + 1 ∣ 2 ^ (2 * e) - 1 := by
      have : 2 ^ (2 * e) - 1 = (2 ^ e + 1) * (2 ^ e - 1) := by
        rw [mul_comm 2 e, pow_mul, ← Nat.sq_sub_sq, one_pow]
      rw [this]; exact dvd_mul_right _ _
    have hm2 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
    have hexp : 4 ^ 2 ^ 2 ^ m = (2 ^ (2 * e)) ^ (2 ^ (2 ^ m - (m + 1))) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, he]
      congr 1
      rw [show 2 * 2 ^ (m + 1) = 2 ^ (m + 2) by ring, ← pow_add, ← pow_succ']
      congr 1
      omega
    rw [hexp]
    exact h1.trans (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ (2 * e)) 1 (2 ^ (2 ^ m - (m + 1))))
