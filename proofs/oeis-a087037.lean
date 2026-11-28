import OMAStatements.S_oeis_a087037
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087037.main) := by
  intro h
  obtain ⟨x, hx, hp⟩ := h 125 (by decide)
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | o
  · by_cases t : 3 ∣ k + k
    · obtain ⟨j, e⟩ := t
      rw [e, pow_mul'] at hp
      have := Nat.le_self_pow (by norm_num : 3 ≠ 0) ((3 * j) ^ j)
      have := hp.eq_one_or_self_of_dvd _ (Odd.nat_add_dvd_pow_add_pow ((3 * j) ^ j) 5 (by decide))
      omega
    · have : (k + k) ^ 2 % 3 = 1 := by
        rcases (by omega : (k + k) % 3 = 1 ∨ (k + k) % 3 = 2) with h | h <;> simp [Nat.pow_mod, h]
      have : (k + k) ^ (k + k) % 3 = 1 := by
        rw [show (k + k) ^ (k + k) = ((k + k) ^ 2) ^ k by rw [← pow_mul, two_mul], Nat.pow_mod, this, one_pow]; rfl
      have := hp.eq_one_or_self_of_dvd 3 (by omega)
      omega
  · have := hp.eq_one_or_self_of_dvd 2 ((o.pow.add_odd (by decide)).two_dvd)
    omega
