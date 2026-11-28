import OMAReductions.R_oeis_a279884_R1

-- Step oeis-a279884.R1.H2: hypothesis H2 of reduction oeis-a279884.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_oeis_a279884_R1.H2 := by
  intro n hn hodd hpow
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n + 1 ≠ 0 by omega)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hpow k (by simpa using hnm)
  have hm3 : 3 ≤ m := by
    obtain ⟨j, rfl⟩ := hm
    omega
  have hn5 : 5 ≤ n := by
    have h1 : n ≠ 1 := by rintro rfl; exact hpow 1 rfl
    have h3 : n ≠ 3 := by rintro rfl; exact hpow 2 rfl
    obtain ⟨j, rfl⟩ := hodd
    omega
  unfold OMA.S_oeis_a279884.f
  set x := n - 1 with hx
  have hx4 : 4 ≤ x := by omega
  have hdvd : x ^ 2 ^ k + 1 ∣ x ^ (n + 1) + 1 := by
    rw [hnm, pow_mul]
    simpa using hm.nat_add_dvd_pow_add_pow (x ^ 2 ^ k) 1
  apply Nat.not_prime_of_dvd_of_lt hdvd
  · have : 1 ≤ x ^ 2 ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  · have hlt : x ^ 2 ^ k < x ^ (n + 1) := by
      apply Nat.pow_lt_pow_right (by omega)
      rw [hnm]
      have : 0 < 2 ^ k := by positivity
      nlinarith
    omega
