import OMAStatements.S_oeis_a255932

open scoped Nat

namespace OMA.P_oeis_a255932

lemma two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]; omega

lemma value_eq (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a255932.value n =
      (((2 * n - 1)‼ ^ 2 : ℕ) : ℝ) / ((2 * n * 4 ^ n : ℕ) : ℝ) := by
  unfold OMA.S_oeis_a255932.value
  rw [Real.Gamma_nat_add_half]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hs : (√Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  push_cast
  rw [div_pow, mul_pow, hs]
  have h4 : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  field_simp

lemma den_le (a b : ℕ) (hb : 0 < b) : (((a : ℚ) / (b : ℚ)).den) ≤ b := by
  have h := Rat.den_dvd (a : ℤ) (b : ℤ)
  rw [Rat.divInt_eq_div] at h
  push_cast at h
  have h' : ((a : ℚ) / (b : ℚ)).den ∣ b := by exact_mod_cast h
  exact Nat.le_of_dvd hb h'

end OMA.P_oeis_a255932

theorem OMA.solution : type_of% @OMA.S_oeis_a255932.main := by
  intro n hn
  refine ⟨(((2 * n - 1)‼ ^ 2 : ℕ) : ℚ) / ((2 * n * 4 ^ n : ℕ) : ℚ), ?_, ?_⟩
  · rw [OMA.P_oeis_a255932.value_eq n hn]
    push_cast
    rfl
  · have hpos : 0 < 2 * n * 4 ^ n := by positivity
    refine le_trans (OMA.P_oeis_a255932.den_le _ _ hpos) ?_
    have h1 := OMA.P_oeis_a255932.two_mul_le_two_pow n
    have h2 : 2 ^ (3 * n) = 2 ^ n * 4 ^ n := by
      rw [show 3 * n = n + 2 * n by ring, pow_add, pow_mul]; norm_num
    rw [h2]
    exact Nat.mul_le_mul_right _ h1
