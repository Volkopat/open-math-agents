import OMAReductions.R_OeisA153330_conjecture2_R2

theorem OMA.solution : OMA.R_OeisA153330_conjecture2_R2.H2 := by
  intro K s h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs : Odd s := by
    by_contra hn
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.1 hn
    have := dvd_trans (dvd_pow_self 3 K.succ_ne_zero) h
    rw [← two_mul, pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod] at this
    norm_num at this
  have hv := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) ⟨1, rfl⟩ (by norm_num) (by norm_num) hs
  have h21 : padicValNat 3 (2 + 1) = 1 := padicValNat_self
  have hK := (padicValNat_dvd_iff_le (by positivity)).1 h
  rw [one_pow] at hv
  exact (padicValNat_dvd_iff_le (by rintro rfl; simp at hs)).2 (by omega)
