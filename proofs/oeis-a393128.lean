import OMAStatements.S_oeis_a393128

-- Disproof at the prime p = 19069, the first prime in A393128 (M. F. Hasler, OEIS A393128:
-- the conjecture fails for the primes in the sequence, the first of which is 19069).
-- f(k) = k + floor(log(pi * k)) is increasing, and pi * 19058 < e^11 < pi * 19059
-- (59872.47 < 59874.14 < 59875.61), so f(19058) = 19068 and f(19059) = 19070: no positive
-- integer k gives 19069.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a393128.main) := by
  intro h
  obtain ⟨k, ⟨hk0, hk⟩, -⟩ := h 19069 (by norm_num)
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have hexp : Real.exp 11 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have lo : (2.7182818283 : ℝ) ^ 11 < Real.exp 11 := by
    rw [hexp]
    exact pow_lt_pow_left₀ e1 (by norm_num) (by norm_num)
  have hi : Real.exp 11 < (2.7182818286 : ℝ) ^ 11 := by
    rw [hexp]
    exact pow_lt_pow_left₀ e2 (Real.exp_pos 1).le (by norm_num)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hpos : 0 < Real.pi * k := mul_pos Real.pi_pos hkpos
  rcases Nat.lt_or_ge k 19059 with hlt | hge
  · have hkle : k ≤ 19058 := by omega
    have hkR : (k : ℝ) ≤ 19058 := by exact_mod_cast hkle
    have hlog : Real.log (Real.pi * k) < 11 := by
      rw [Real.log_lt_iff_lt_exp hpos]
      calc Real.pi * k ≤ 3.141593 * 19058 := by nlinarith
        _ < (2.7182818283 : ℝ) ^ 11 := by norm_num
        _ < Real.exp 11 := lo
    have hfl : ⌊Real.log (Real.pi * k)⌋ < 11 := Int.floor_lt.mpr (by exact_mod_cast hlog)
    have hkZ : (k : ℤ) ≤ 19058 := by exact_mod_cast hkle
    omega
  · have hkR : (19059 : ℝ) ≤ k := by exact_mod_cast hge
    have hlog : 11 < Real.log (Real.pi * k) := by
      rw [Real.lt_log_iff_exp_lt hpos]
      calc Real.exp 11 < (2.7182818286 : ℝ) ^ 11 := hi
        _ < 3.141592 * 19059 := by norm_num
        _ ≤ Real.pi * k := by nlinarith
    have hfl : (11 : ℤ) ≤ ⌊Real.log (Real.pi * k)⌋ := Int.le_floor.mpr (by exact_mod_cast hlog.le)
    have hkZ : (19059 : ℤ) ≤ k := by exact_mod_cast hge
    omega
