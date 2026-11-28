import OMAStatements.S_oeis_a189045

theorem OMA.solution : type_of% @OMA.S_oeis_a189045.main := by
  rintro n p q ⟨_, m, k, hk, hm⟩ hp _ hn rfl
  subst hn
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rcases hp.eq_two_or_odd' with rfl | ⟨r, rfl⟩
  · have hm2 : m ≤ 2 := by
      by_contra h
      have h1 : 3 ^ (j + 2) ≤ m ^ (j + 2) := Nat.pow_le_pow_left (by omega) _
      have h2 : 3 ^ 2 ≤ 3 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases m
    · simp at hm
    · simp at hm
    · have h4 : (2:ℕ) ^ (j + 2) = 4 * 2 ^ j := by ring
      omega
  · have hsq : (2 * r + 1) * (2 * r + 1) = 4 * (r * r) + 4 * r + 1 := by ring
    rcases Nat.even_or_odd m with ⟨s, rfl⟩ | hodd
    · have hd : 4 ∣ (s + s) ^ (j + 2) := ⟨s ^ 2 * (s + s) ^ j, by ring⟩
      omega
    · obtain ⟨t, ht⟩ := hodd.pow (n := j + 2)
      omega

