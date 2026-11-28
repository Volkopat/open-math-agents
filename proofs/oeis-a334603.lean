import OMAStatements.S_oeis_a334603

namespace OMA.P_oeis_a334603

open OMA.S_oeis_a334603

lemma ten_pow_eq_one_iff (n m : ℕ) : (10 : ZMod (11 ^ n)) ^ m = 1 ↔ 11 ^ n ∣ 10 ^ m - 1 := by
  have h1 : 1 ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
  rw [show (10 : ZMod (11 ^ n)) ^ m = ((10 ^ m : ℕ) : ZMod (11 ^ n)) by push_cast; rfl]
  rw [show (1 : ZMod (11 ^ n)) = ((1 : ℕ) : ZMod (11 ^ n)) by simp]
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' h1]

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

lemma val_99 : padicValNat 11 99 = 1 := by
  rw [show (99 : ℕ) = 11 * 9 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]

lemma val_pow (k : ℕ) : padicValNat 11 (100 ^ (11 ^ k) - 1) = k + 1 := by
  have h := padicValNat.pow_sub_pow (p := 11) (x := 100) (y := 1) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (n := 11 ^ k) (by positivity)
  rw [one_pow] at h
  rw [h, show (100 : ℕ) - 1 = 99 by norm_num, val_99, padicValNat.prime_pow]
  ring

lemma ne_zero_pow (k : ℕ) : 100 ^ (11 ^ k) - 1 ≠ 0 := by
  have : 100 ≤ 100 ^ (11 ^ k) := Nat.le_self_pow (by positivity) _
  omega

lemma ten_pow_two (j : ℕ) : 10 ^ (2 * j) = 100 ^ j := by
  rw [pow_mul]; norm_num

lemma odd_pow_mod (j : ℕ) (hj : Odd j) : 10 ^ j % 11 = 10 := by
  obtain ⟨i, rfl⟩ := hj
  rw [pow_succ, ten_pow_two, Nat.mul_mod, Nat.pow_mod]
  norm_num

end OMA.P_oeis_a334603

open OMA.P_oeis_a334603 in
theorem OMA.solution : type_of% @OMA.S_oeis_a334603.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  unfold OMA.S_oeis_a334603.a OMA.S_oeis_a334603.period
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · rw [ten_pow_eq_one_iff, ten_pow_two, padicValNat_dvd_iff_le (ne_zero_pow k), val_pow]
  · intro p hp hpd
    have hp' : p = 2 ∨ p = 11 := by
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      · right; exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h)
    rcases hp' with rfl | rfl
    · rw [show 2 * 11 ^ k / 2 = 11 ^ k by omega, Ne, ten_pow_eq_one_iff]
      intro h
      have h11 : 11 ∣ 10 ^ (11 ^ k) - 1 := (dvd_pow_self 11 (by omega)).trans h
      have hm := odd_pow_mod (11 ^ k) (Odd.pow (by decide))
      have h1 : 1 ≤ 10 ^ (11 ^ k) := Nat.one_le_pow _ _ (by norm_num)
      generalize 10 ^ (11 ^ k) = X at h11 hm h1
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exfalso
          simp at hpd
        · exact ⟨k - 1, by omega⟩
      rw [show 2 * 11 ^ (j + 1) / 11 = 2 * 11 ^ j by rw [pow_succ]; omega, Ne, ten_pow_eq_one_iff,
        ten_pow_two, padicValNat_dvd_iff_le (ne_zero_pow j), val_pow]
      omega
