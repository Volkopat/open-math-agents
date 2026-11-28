import OMAStatements.S_oeis_a176328

/-! For odd indices above one the Bernoulli number vanishes, leaving an odd numerator. -/

open OMA.S_oeis_a176328 in
theorem OMA.solution : type_of% @OMA.S_oeis_a176328.main := by
  intro n
  have h₂ : (Polynomial.bernoulli (2 * n + 1)).eval 2 = bernoulli' (2 * n + 1) + ↑(2 * n + 1) := by
    simpa [show (1 : ℚ) + 1 = 2 by norm_num, Polynomial.bernoulli_eval_one] using
      Polynomial.bernoulli_eval_one_add (2 * n + 1) 1
  have hp : (-1 : ℚ) ^ (2 * n + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [a, Polynomial.bernoulli_eval_one, h₂, hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [bernoulli'_one]
  · rw [bernoulli'_eq_zero_of_odd ⟨n, rfl⟩ (by omega)]
    have hc : Nat.Coprime (-(2 * (n : ℤ) + 1)).natAbs (2 : ℤ).natAbs := by
      rw [Int.natAbs_neg, show (2 * (n : ℤ) + 1).natAbs = 2 * n + 1 by omega]
      exact Nat.coprime_two_right.mpr ⟨n, rfl⟩
    have h := Rat.num_div_eq_of_coprime (by decide : (0 : ℤ) < 2) hc
    push_cast at h ⊢
    simpa using h
