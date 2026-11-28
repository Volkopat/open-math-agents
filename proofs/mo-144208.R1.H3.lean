import OMAReductions.R_mo_144208_R1

namespace MoHelp

theorem pow3_mod8 (c : ℕ) : 3 ^ c % 8 = 1 ∨ 3 ^ c % 8 = 3 := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> simp [h]

theorem two_pow_mod8 (c : ℕ) (hc : 3 ≤ c) : 2 ^ c % 8 = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  have : 2 ^ (3 + d) = 8 * 2 ^ d := by ring
  rw [this, Nat.mul_mod_right]

theorem four_pow_mod8 (c : ℕ) (hc : 2 ≤ c) : 4 ^ c % 8 = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  have : 4 ^ (2 + d) = 8 * (2 * 4 ^ d) := by ring
  rw [this, Nat.mul_mod_right]

theorem two_pow_mod2 (a : ℕ) (ha : 0 < a) : 2 ^ a % 2 = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [pow_add]; simp

theorem three_pow_mod2 (a : ℕ) : 3 ^ a % 2 = 1 := by
  rw [Nat.pow_mod]; simp

theorem eight_dvd (S b : ℕ) (hS : 2 ∣ S) (hb : 3 ≤ b) : 8 ∣ S ^ b :=
  (pow_dvd_pow 2 hb).trans (pow_dvd_pow_of_dvd hS b)

theorem bound4 (a : ℕ) (ha : 2 ≤ a) : 1 + 2 ^ a + 3 ^ a < 4 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a _ ih => rw [pow_succ, pow_succ, pow_succ]; omega

theorem bound3 (a : ℕ) (ha : 2 ≤ a) : 9 * (1 + 2 ^ a) ≤ 5 * 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a _ ih => rw [pow_succ, pow_succ]; omega

end MoHelp

open MoHelp in
theorem OMA.solution : OMA.R_mo_144208_R1.H3 := by
  intro a b c ha hb hc h
  have hc3 : 3 ≤ c := by nlinarith
  have hS : 2 ∣ 1 + 2 ^ a + 3 ^ a + 4 ^ a := by
    have := two_pow_mod2 a ha
    have := three_pow_mod2 a
    have := four_pow_mod8 1
    have h4 : 4 ^ a % 2 = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
      rw [pow_add]; simp [Nat.mul_mod]
    omega
  by_cases hb3 : 3 ≤ b
  · have h8 := eight_dvd _ b hS hb3
    rw [h] at h8
    have := two_pow_mod8 c hc3
    have := four_pow_mod8 c (by omega)
    rcases pow3_mod8 c with h3 | h3 <;> omega
  · obtain rfl : b = 2 := by omega
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · obtain rfl : a = 1 := by omega
      have h' : (100 : ℕ) = 1 + 2 ^ c + 3 ^ c + 4 ^ c := by rw [← h]; norm_num
      rcases Nat.lt_or_ge c 4 with hc4 | hc4
      · obtain rfl : c = 3 := by omega
        rfl
      · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) hc4
        norm_num at this
        have := Nat.zero_le (2 ^ c)
        have := Nat.zero_le (3 ^ c)
        linarith
    · have hlt := bound4 a ha2
      have hS2 : (1 + 2 ^ a + 3 ^ a + 4 ^ a) ^ 2 < (2 * 4 ^ a) ^ 2 :=
        Nat.pow_lt_pow_left (by omega) (by norm_num)
      have he : (2 * 4 ^ a) ^ 2 = 4 ^ (2 * a + 1) := by ring
      have hle := Nat.pow_le_pow_right (by norm_num : 0 < 4) (show 2 * a + 1 ≤ c by omega)
      have hk : 1 + 2 ^ c + 3 ^ c + 4 ^ c < 4 ^ (2 * a + 1) := by rw [← h, ← he]; exact hS2
      have := Nat.zero_le (2 ^ c)
      have := Nat.zero_le (3 ^ c)
      linarith

