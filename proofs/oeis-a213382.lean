import OMAStatements.S_oeis_a213382
theorem OMA.solution : type_of% @OMA.S_oeis_a213382.main := by
  rintro k (rfl | hk)
  · norm_num
  obtain rfl | rfl | rfl | h := (by have := hk.two_le; omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k)
  · norm_num
  · norm_num
  · norm_num at hk
  have := Fact.mk hk
  have a : (3 * k - 2) ^ (3 * k - 2) ≡ 3 * k - 2 [MOD k] := by
    have : ((3 * k - 2 : ℕ) : ZMod k) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro d
      have := Nat.le_of_dvd two_pos (by simpa [show 3 * k - (3 * k - 2) = 2 by omega] using Nat.dvd_sub (dvd_mul_left k 3) d)
      omega
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, show 3 * k - 2 = (k - 1) * 3 + 1 by omega,
      pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one (by rwa [← show 3 * k - 2 = (k - 1) * 3 + 1 by omega]), one_pow, one_mul]
  have b : (3 * k - 2) ^ (3 * k - 2) ≡ 3 * k - 2 [MOD 3] :=
    ((show 3 * k - 2 ≡ 1 [MOD 3] by unfold Nat.ModEq; omega).pow _).trans (by rw [one_pow]; unfold Nat.ModEq; omega)
  rw [(Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes Nat.prime_three hk).2 (by omega))).1 ⟨b, a⟩]
  exact Nat.mod_eq_of_lt (by omega)
