import OMAStatements.S_oeis_a364555

lemma a364555_tri_div (k n : ℕ) (h : k * (k + 1) = 2 * n) : k * (k + 1) / 2 = n := by
  rw [h]; omega

lemma a364555_tri_mul (k n : ℕ) (h : k * (k + 1) / 2 = n) : k * (k + 1) = 2 * n := by
  have : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a364555.main := by
  intro m hm
  unfold OMA.S_oeis_a364555.InSeq
  constructor
  · rintro ⟨-, h⟩ d hd q hq
    rw [Nat.mem_divisors] at hd
    obtain ⟨r, hr⟩ := hd.1
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hmr : m / d = r := by rw [hr]; exact Nat.mul_div_cancel_left r hd0
    rw [hmr]
    refine ⟨fun he => h ⟨q * d, q, hq, a364555_tri_div _ _ ?_⟩, fun he => h ⟨2 * r, q, hq, a364555_tri_div _ _ ?_⟩,
      fun he => h ⟨q * (2 * d), q, hq, a364555_tri_div _ _ ?_⟩, fun he => h ⟨r, q, hq, a364555_tri_div _ _ ?_⟩⟩
    · rw [show q * d + 1 = 2 * r by omega, hr]; ring
    · rw [show 2 * r + 1 = q * d by omega, hr]; ring
    · rw [show q * (2 * d) + 1 = r by omega, hr]; ring
    · rw [show r + 1 = q * (2 * d) by omega, hr]; ring
  · intro h
    refine ⟨hm, ?_⟩
    rintro ⟨k, p, hp, hk⟩
    have hk2 := a364555_tri_mul _ _ hk
    have hp0 := hp.pos
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ k * (k + 1) from ⟨2 * m, by rw [hk2]; ring⟩) with
      ⟨t, ht⟩ | ⟨t, ht⟩
    · -- k = p * t
      have htu : t * (k + 1) = 2 * m := by
        apply Nat.eq_of_mul_eq_mul_left hp0
        rw [← mul_assoc, ← ht, hk2]; ring
      rcases Nat.even_or_odd t with ⟨d, hdd⟩ | ⟨c, hc⟩
      · have hmd : m = d * (k + 1) := by subst hdd; linarith
        have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hmd; omega)
        have hdm : d ∈ m.divisors := Nat.mem_divisors.2 ⟨⟨k + 1, hmd⟩, by omega⟩
        have hmr : m / d = k + 1 := by rw [hmd]; exact Nat.mul_div_cancel_left _ hd0
        apply (h d hdm p hp).2.2.1
        rw [hmr, ht, hdd, Nat.add_sub_cancel]; ring
      · have h2 : 2 ∣ k + 1 := by
          have : 2 ∣ t * (k + 1) := ⟨m, htu⟩
          rcases (Nat.Prime.dvd_mul Nat.prime_two).1 this with h' | h'
          · omega
          · exact h'
        obtain ⟨r, hr⟩ := h2
        have hmd : m = t * r := by rw [hr] at htu; linarith
        have ht0 : 0 < t := by omega
        have hdm : t ∈ m.divisors := Nat.mem_divisors.2 ⟨⟨r, hmd⟩, by omega⟩
        have hmr : m / t = r := by rw [hmd]; exact Nat.mul_div_cancel_left _ ht0
        apply (h t hdm p hp).1
        rw [hmr]; omega
    · -- k + 1 = p * t
      have htu : k * t = 2 * m := by
        apply Nat.eq_of_mul_eq_mul_left hp0
        have : k * (p * t) = 2 * (m * p) := by rw [← ht]; exact hk2
        linarith
      rcases Nat.even_or_odd t with ⟨d, hdd⟩ | ⟨c, hc⟩
      · have hmd : m = d * k := by subst hdd; linarith
        have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
        have hdm : d ∈ m.divisors := Nat.mem_divisors.2 ⟨⟨k, hmd⟩, by omega⟩
        have hmr : m / d = k := by rw [hmd]; exact Nat.mul_div_cancel_left _ hd0
        apply (h d hdm p hp).2.2.2
        rw [hmr, ht, hdd]; ring
      · have h2 : 2 ∣ k := by
          have : 2 ∣ k * t := ⟨m, htu⟩
          rcases (Nat.Prime.dvd_mul Nat.prime_two).1 this with h' | h'
          · exact h'
          · omega
        obtain ⟨r, hr⟩ := h2
        have hmd : m = t * r := by rw [hr] at htu; linarith
        have ht0 : 0 < t := by omega
        have hdm : t ∈ m.divisors := Nat.mem_divisors.2 ⟨⟨r, hmd⟩, by omega⟩
        have hmr : m / t = r := by rw [hmd]; exact Nat.mul_div_cancel_left _ ht0
        apply (h t hdm p hp).2.1
        rw [hmr]; omega
