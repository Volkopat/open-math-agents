import OMAStatements.S_oeis_a195507


def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

lemma a_eq (n : ℕ) : OMA.S_oeis_a195507.a n = n + L (n - 1) := by
  have hmem : ∀ m, m ∈ {m : ℕ | n < m ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → m % k = n % k} ↔
      n < m ∧ L (n - 1) ∣ m - n := by
    intro m
    simp only [Set.mem_ofPred_eq, L, Finset.lcm_dvd_iff, Finset.mem_Icc, id]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k hk => ?_⟩
      exact (Nat.modEq_iff_dvd' h1.le).1 (h2 k hk.1 hk.2).symm
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k hk1 hk2 => ?_⟩
      exact ((Nat.modEq_iff_dvd' h1.le).2 (h2 k ⟨hk1, hk2⟩)).symm
  have hLpos : 0 < L (n - 1) := by
    unfold L
    apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]
    simp
  unfold OMA.S_oeis_a195507.a
  apply le_antisymm
  · apply Nat.sInf_le
    rw [hmem]
    refine ⟨by omega, ?_⟩
    simp
  · apply le_csInf
    · exact ⟨n + L (n - 1), (hmem _).2 ⟨by omega, by simp⟩⟩
    · intro m hm
      rw [hmem] at hm
      have := Nat.le_of_dvd (by omega) hm.2
      omega

lemma L_succ (n : ℕ) : L (n + 1) = Nat.lcm (n + 1) (L n) := by
  unfold L
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert]
  rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a195507.main := by
  intro n hn
  rw [a_eq, a_eq]
  simp only [Nat.add_sub_cancel]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set K := L m
  set N := m + 1 with hN
  have hKpos : 0 < K := by
    show 0 < L m
    unfold L
    apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]
    simp
  rw [L_succ]
  set g := Nat.gcd N K with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left N K
  obtain ⟨k', hk'⟩ := Nat.gcd_dvd_right N K
  rw [← hg] at hn' hk'
  have hcop : Nat.Coprime n' k' := by
    have := Nat.coprime_div_gcd_div_gcd (m := N) (n := K) hgpos
    rw [← hg] at this
    rw [hn', hk', Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos] at this
    exact this
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h] at hn'; omega
    · exact h
  have hden : (((N + K : ℕ) : ℚ) / (N : ℕ)).den = n' := by
    have h1 : (((N + K : ℕ) : ℚ) / (N : ℕ)) = ((((n' + k' : ℕ) : ℤ) : ℚ) / ((n' : ℕ) : ℤ)) := by
      rw [hn', hk']
      push_cast
      have : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
      have : (n' : ℚ) ≠ 0 := by exact_mod_cast hn'pos.ne'
      field_simp
    rw [h1]
    have := Rat.den_div_eq_of_coprime (a := ((n' + k' : ℕ) : ℤ)) (b := ((n' : ℕ) : ℤ))
      (by exact_mod_cast hn'pos) (by
        simp only [Int.natAbs_natCast]
        rw [add_comm]; exact Nat.coprime_add_self_left.2 hcop.symm)
    exact_mod_cast this
  rw [hden]
  have hlcm : Nat.lcm N K = n' * K := by
    rw [Nat.lcm, ← hg]
    conv_lhs => rw [hn']
    rw [mul_assoc, Nat.mul_div_cancel_left _ hgpos]
  rw [hlcm]
  push_cast
  ring
