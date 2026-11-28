import OMAStatements.S_oeis_a308833

lemma OMA.a308833_six_dvd (r : ℕ) : 6 ∣ r * (r + 1) * (r + 2) := by
  have h : r % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod r, Nat.add_mod r, Nat.add_mod r]
  interval_cases r % 6 <;> norm_num

lemma OMA.a308833_T_mul (r : ℕ) : OMA.S_oeis_a308833.T r * 6 = r * (r + 1) * (r + 2) :=
  Nat.div_mul_cancel (OMA.a308833_six_dvd r)

lemma OMA.a308833_pair {i j n : ℕ} (hi : 0 < i) (hij : i < j) (hjn : j ≤ n) :
    i * j ∣ Nat.factorial n := by
  have h1 : i ∣ Nat.factorial (j - 1) := Nat.dvd_factorial hi (by omega)
  have h2 : i * j ∣ Nat.factorial j := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.factorial_succ, mul_comm]
    exact Nat.mul_dvd_mul_left _ (by simpa using h1)
  exact h2.trans (Nat.factorial_dvd_factorial hjn)

/-- An odd composite `N` divides `(N - 3)!`. -/
lemma OMA.a308833_comp {N : ℕ} (hodd : Odd N) (h1 : 1 < N) (hnp : ¬ N.Prime) :
    N ∣ Nat.factorial (N - 3) := by
  set a := N.minFac with ha
  have hap : a.Prime := Nat.minFac_prime (by omega)
  obtain ⟨b, hb⟩ : a ∣ N := Nat.minFac_dvd N
  have ha2 : a ≠ 2 := by
    intro h
    have : 2 ∣ N := h ▸ Nat.minFac_dvd N
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have ha3 : 3 ≤ a := by have := hap.two_le; omega
  have hb2 : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b
      · omega
      · rw [mul_one] at hb; exact absurd (hb ▸ hap) hnp
    · exact h
  have hab : a ≤ b := Nat.minFac_le_of_dvd hb2 (Dvd.intro_left _ hb.symm)
  rcases Nat.lt_or_ge a b with hlt | hge
  · rw [hb]
    have h3b : 3 * b ≤ N := by rw [hb]; exact Nat.mul_le_mul_right b ha3
    exact OMA.a308833_pair (by omega) hlt (by omega)
  · have hab' : a = b := le_antisymm hab hge
    rw [← hab'] at hb
    have h3a : 3 * a ≤ N := by rw [hb]; exact Nat.mul_le_mul_right a ha3
    have : a * (2 * a) ∣ Nat.factorial (N - 3) :=
      OMA.a308833_pair (by omega) (by omega) (by omega)
    exact (hb ▸ Dvd.intro (2 : ℕ) (by ring) : N ∣ a * (2 * a)).trans this

theorem OMA.solution : type_of% @OMA.S_oeis_a308833.main := by
  intro r hodd hr
  have hr3 : 3 ≤ r := by obtain ⟨k, rfl⟩ := hodd; omega
  have hT0 := OMA.a308833_T_mul r
  have hT1 := OMA.a308833_T_mul (r + 1)
  by_cases hp : (r + 2).Prime
  · -- r + 2 prime: neither r nor r + 1 is a term
    have hnd : ∀ n, n < r + 2 → ¬ (r + 2 ∣ 6 * Nat.factorial n) := by
      intro n hn h
      rcases (Nat.Prime.dvd_mul hp).mp h with h6 | hf
      · have := Nat.le_of_dvd (by norm_num) h6
        have hr4 : r ≤ 4 := by omega
        interval_cases r
        · omega
        · norm_num at hp
      · exact absurd ((Nat.Prime.dvd_factorial hp).mp hf) (by omega)
    have nA : ¬ OMA.S_oeis_a308833.IsTerm r := by
      intro h
      apply hnd r (by omega)
      have : OMA.S_oeis_a308833.T r * 6 ∣ Nat.factorial r * 6 := Nat.mul_dvd_mul_right h 6
      rw [hT0, mul_comm (Nat.factorial r)] at this
      exact (Dvd.intro_left _ rfl).trans this
    have nB : ¬ OMA.S_oeis_a308833.IsTerm (r + 1) := by
      intro h
      apply hnd (r + 1) (by omega)
      have : OMA.S_oeis_a308833.T (r + 1) * 6 ∣ Nat.factorial (r + 1) * 6 :=
        Nat.mul_dvd_mul_right h 6
      rw [hT1, mul_comm (Nat.factorial (r + 1))] at this
      exact (Dvd.intro ((r + 1) * (r + 3)) (by ring)).trans this
    exact ⟨iff_of_false nA nB, iff_of_false nB (fun h => h.2 hp)⟩
  · -- r + 2 composite: both are terms
    have hN : r + 2 ∣ Nat.factorial (r - 1) := by
      have := OMA.a308833_comp (N := r + 2) (by simpa [Nat.odd_add] using hodd) (by omega) hp
      simpa using this
    obtain ⟨k, hk⟩ := hodd
    -- r + 2 ≥ 9
    have hr7 : 7 ≤ r := by
      rcases (show r = 3 ∨ r = 5 ∨ 7 ≤ r by omega) with h | h | h
      · subst h; exact absurd (by norm_num : Nat.Prime 5) hp
      · subst h; exact absurd (by norm_num : Nat.Prime 7) hp
      · exact h
    have A : OMA.S_oeis_a308833.IsTerm r := by
      unfold OMA.S_oeis_a308833.IsTerm
      have h2 : 2 * (k + 1) ∣ Nat.factorial (r - 1) :=
        OMA.a308833_pair (by norm_num) (by omega) (by omega)
      have hc : Nat.Coprime (r + 1) (r + 2) := by
        have := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (r + 1))
        simpa [add_assoc] using this
      have h12 : (r + 1) * (r + 2) ∣ Nat.factorial (r - 1) :=
        hc.mul_dvd_of_dvd_of_dvd (by rw [show r + 1 = 2 * (k + 1) by omega]; exact h2) hN
      have hfac : Nat.factorial r = r * Nat.factorial (r - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
        simp [Nat.factorial_succ]
      have : r * (r + 1) * (r + 2) ∣ Nat.factorial r := by
        rw [hfac, mul_assoc]; exact Nat.mul_dvd_mul_left r h12
      rw [← hT0] at this
      exact (Dvd.intro _ rfl).trans this
    have B : OMA.S_oeis_a308833.IsTerm (r + 1) := by
      unfold OMA.S_oeis_a308833.IsTerm
      have h2 : 2 * (k + 2) ∣ Nat.factorial r :=
        OMA.a308833_pair (by norm_num) (by omega) (by omega)
      have hN' : r + 2 ∣ Nat.factorial r :=
        hN.trans (Nat.factorial_dvd_factorial (by omega))
      have hc : Nat.Coprime (r + 2) (r + 3) := by
        have := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (r + 2))
        simpa [add_assoc] using this
      have h23 : (r + 2) * (r + 3) ∣ Nat.factorial r :=
        hc.mul_dvd_of_dvd_of_dvd hN' (by rw [show r + 3 = 2 * (k + 2) by omega]; exact h2)
      have : (r + 1) * (r + 1 + 1) * (r + 1 + 2) ∣ Nat.factorial (r + 1) := by
        rw [Nat.factorial_succ, mul_assoc]
        exact Nat.mul_dvd_mul_left (r + 1) h23
      rw [← hT1] at this
      exact (Dvd.intro _ rfl).trans this
    exact ⟨iff_of_true A B, iff_of_true B ⟨by omega, hp⟩⟩
