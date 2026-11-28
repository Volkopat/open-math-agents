import OMAReductions.R_oeis_a279884_R1

theorem OMA.solution : OMA.R_oeis_a279884_R1.H1 := by
  intro n hn4 hnEven hp
  obtain ⟨m, hm⟩ := hnEven
  have hm2 : 2 ≤ m := by omega
  have hodd : Odd (n - 1) := by
    refine ⟨m - 1, ?_⟩
    omega
  have hpow : Odd ((n - 1) ^ (n + 1)) := hodd.pow
  have heven : Even (OMA.S_oeis_a279884.f n) := by
    unfold OMA.S_oeis_a279884.f
    exact hpow.add_one
  have hgt : 2 < OMA.S_oeis_a279884.f n := by
    unfold OMA.S_oeis_a279884.f
    have h3 : 3 ≤ n - 1 := by omega
    have hle : 3 ^ 5 ≤ (n - 1) ^ (n + 1) := by
      calc 3 ^ 5 ≤ 3 ^ (n + 1) := pow_le_pow_right' (by norm_num) (by omega)
        _ ≤ (n - 1) ^ (n + 1) := pow_le_pow_left' h3 _
    have h243 : (3 : ℕ) ^ 5 = 243 := by norm_num
    omega
  rcases hp.eq_two_or_odd' with h2 | ho
  · omega
  · exact (Nat.not_odd_iff_even.mpr heven) ho
