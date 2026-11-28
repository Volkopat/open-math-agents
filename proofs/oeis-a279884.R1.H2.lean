import OMAReductions.R_oeis_a279884_R1

theorem OMA.solution : OMA.R_oeis_a279884_R1.H2 := by
  intro n hn hodd hpow
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_two_pow_mul_odd (show n + 1 ≠ 0 by omega)
  have : m ≠ 1 := by rintro rfl; exact hpow k (by simpa using h)
  have : n ≠ 1 := by rintro rfl; exact hpow 1 rfl
  have : n ≠ 3 := by rintro rfl; exact hpow 2 rfl
  have : 4 ≤ n - 1 := by obtain ⟨i, rfl⟩ := hodd; omega
  have hd : (n - 1) ^ 2 ^ k + 1 ∣ (n - 1) ^ (n + 1) + 1 := by
    rw [h, pow_mul]; simpa using hm.nat_add_dvd_pow_add_pow ((n - 1) ^ 2 ^ k) 1
  have := Nat.pow_lt_pow_right (show 1 < n - 1 by omega) (show 2 ^ k < n + 1 by
    rw [h]; nlinarith [Nat.one_le_two_pow (n := k), show 3 ≤ m by obtain ⟨j, rfl⟩ := hm; omega])
  exact Nat.not_prime_of_dvd_of_lt hd (by nlinarith [Nat.one_le_pow (2 ^ k) (n - 1) (by omega)]) (Nat.add_lt_add_right this 1)
