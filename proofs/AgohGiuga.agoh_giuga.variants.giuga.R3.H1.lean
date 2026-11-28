import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3.H1 := by
  intro m D q k hm hq h
  obtain ⟨t, ht⟩ : ∃ t, D + t = m * k :=
    ⟨m * k - D, by have := Nat.lt_of_mul_lt_mul_left (by nlinarith : q * D < q * (m * k)); omega⟩
  have e : q * t + 1 = m := by nlinarith
  have : 0 < t ∧ t < m := ⟨by nlinarith, by nlinarith⟩
  obtain _ | k := k
  · omega
  rw [show D = m - t + m * k by rw [Nat.mul_succ] at ht; omega, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega), show m - (m - t) = t by omega]
  omega
