import OMAStatements.S_oeis_a216440

-- Problem: A216440: a(n) = smallest m such that 2n-1 | 2^m+1, or 0 if no such m exists.
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)

open OMA.S_oeis_a216440

theorem deck_inv (k : ℕ) : ∀ m j, j < 2 * k →
    deck k m j < 2 * k ∧ (2 ^ m * (deck k m j + 1) : ℤ) ≡ j + 1 [ZMOD (2 * k + 1)] := by
  intro m
  induction m with
  | zero => intro j hj; simp [deck, hj]
  | succ m ih =>
    intro j hj
    have h1 : src k j < 2 * k := by unfold src; split_ifs <;> omega
    have h2 : (2 * ((src k j : ℤ) + 1)) ≡ j + 1 [ZMOD (2 * k + 1)] := by
      unfold src
      split_ifs with h
      · apply Int.modEq_iff_dvd.mpr
        refine ⟨-1, ?_⟩
        push_cast
        have : (j : ℤ) % 2 = 0 := by omega
        omega
      · apply Int.modEq_iff_dvd.mpr
        refine ⟨0, ?_⟩
        push_cast
        omega
    obtain ⟨a, b⟩ := ih (src k j) h1
    refine ⟨a, ?_⟩
    show (2 ^ (m+1) * (deck k m (src k j) + 1) : ℤ) ≡ _ [ZMOD _]
    calc (2 ^ (m+1) * (deck k m (src k j) + 1) : ℤ)
        = 2 * (2 ^ m * (deck k m (src k j) + 1)) := by ring
      _ ≡ 2 * ((src k j : ℤ) + 1) [ZMOD _] := b.mul_left 2
      _ ≡ _ [ZMOD _] := h2

theorem rev_iff (n m : ℕ) (hn : 1 ≤ n) : Reverses (n - 1) m ↔ (2 * n - 1) ∣ 2 ^ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e1 : k + 1 - 1 = k := by omega
  have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [e1, e2]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Reverses]
  constructor
  · intro h
    have h0 := h 0 (by omega)
    obtain ⟨_, hc⟩ := deck_inv k m 0 (by omega)
    rw [h0] at hc
    have hc' := Int.ModEq.dvd hc.symm
    have e0 : ((2 * k - 1 - 0 : ℕ) : ℤ) = 2 * k - 1 := by omega
    rw [e0] at hc'
    have hd : ((2 * k + 1 : ℕ) : ℤ) ∣ ((2 ^ m + 1 : ℕ) : ℤ) := by
      push_cast at hc' ⊢
      have : (2 : ℤ) ^ m + 1 = (2 * k + 1) * 2 ^ m - (2 ^ m * (2 * k - 1 + 1) - (0 + 1)) := by ring
      rw [this]
      exact dvd_sub (dvd_mul_right _ _) hc'
    exact_mod_cast hd
  · intro h j hj
    obtain ⟨hlt, hc⟩ := deck_inv k m j hj
    have hd : (2 * (k : ℤ) + 1) ∣ (2 ^ m + 1) := by exact_mod_cast h
    have hc' := Int.ModEq.dvd hc.symm
    have h3 : (2 * (k : ℤ) + 1) ∣ ((deck k m j : ℤ) + j + 2) := by
      have : ((deck k m j : ℤ) + j + 2) = ((deck k m j : ℤ) + 1) * (2 ^ m + 1) - (2 ^ m * ((deck k m j : ℤ) + 1) - (j + 1)) := by ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hd _) hc'
    obtain ⟨c, hc2⟩ := h3
    have hc3 : c = 1 := by
      have a1 : (0 : ℤ) < c := by
        by_contra hneg
        push Not at hneg
        nlinarith
      have a2 : c < 2 := by
        by_contra hneg
        push Not at hneg
        have : (deck k m j : ℤ) < 2 * k := by exact_mod_cast hlt
        have : (j : ℤ) < 2 * k := by exact_mod_cast hj
        nlinarith
      omega
    subst hc3
    show deck k m j = 2 * k - 1 - j
    omega

open Classical in
theorem OMA.solution : type_of% @OMA.S_oeis_a216440.main := by
  intro n hn
  have key := rev_iff n
  unfold shuffles a
  by_cases h : ∃ m, 1 ≤ m ∧ (2 * n - 1) ∣ 2 ^ m + 1
  · have h' : ∃ m, 1 ≤ m ∧ Reverses (n - 1) m := by
      obtain ⟨m, hm, hd⟩ := h
      exact ⟨m, hm, (key m hn).2 hd⟩
    rw [dif_pos h, dif_pos h']
    apply le_antisymm
    · exact Nat.find_min' h' ⟨(Nat.find_spec h).1, (key _ hn).2 (Nat.find_spec h).2⟩
    · exact Nat.find_min' h ⟨(Nat.find_spec h').1, (key _ hn).1 (Nat.find_spec h').2⟩
  · have h' : ¬ ∃ m, 1 ≤ m ∧ Reverses (n - 1) m := by
      rintro ⟨m, hm, hr⟩
      exact h ⟨m, hm, (key m hn).1 hr⟩
    rw [dif_neg h, dif_neg h']
