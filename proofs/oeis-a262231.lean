import OMAStatements.S_oeis_a262231

-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)

open OMA.S_oeis_a262231

theorem sel_iff (n : ℕ) : selected n ↔ 2 ≤ n ∧ ∀ k : ℕ, k < n → selected k → ¬ (k + 1) ∣ n := by
  rw [selected]

theorem sel_two : selected 2 := by
  rw [sel_iff]
  refine ⟨le_rfl, fun k hk hs => ?_⟩
  have := ((sel_iff k).1 hs).1
  omega

theorem not_sel_of_three (n : ℕ) (h : 3 ∣ n) : ¬ selected n := by
  intro hs
  rw [sel_iff] at hs
  obtain ⟨h2, hall⟩ := hs
  have h3 : 3 ≤ n := by
    obtain ⟨c, hc⟩ := h
    omega
  exact hall 2 (by omega) sel_two h

theorem sel_of_prime (q : ℕ) (hq : q.Prime) (h : ¬ selected (q - 1)) : selected q := by
  rw [sel_iff]
  refine ⟨hq.two_le, fun k hk hs hd => ?_⟩
  rcases (Nat.dvd_prime hq).1 hd with h1 | h1
  · have : k = 0 := by omega
    subst this
    have := ((sel_iff 0).1 hs).1
    omega
  · apply h
    have : q - 1 = k := by omega
    rw [this]; exact hs

theorem OMA.solution : type_of% @OMA.S_oeis_a262231.main := by
  intro hT N
  obtain ⟨p, hp, hpp, hp2⟩ := hT (N + 4)
  have h5 : 5 ≤ p := by
    by_contra hlt
    omega
  have h3 : 3 ∣ p + 1 := by
    have hm : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hm with hm | hm | hm
    · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hm
      have := (Nat.dvd_prime hpp).1 this
      omega
    · have : 3 ∣ p + 2 := by omega
      have := (Nat.dvd_prime hp2).1 this
      omega
    · omega
  have hs2 : selected (p + 2) := by
    apply sel_of_prime _ hp2
    have : p + 2 - 1 = p + 1 := by omega
    rw [this]
    exact not_sel_of_three _ h3
  by_cases hs : selected (p - 1)
  · exact ⟨p - 1, p + 2, by omega, by omega, by omega, hs, hs2⟩
  · exact ⟨p, p + 2, by omega, by omega, by omega, sel_of_prime p hpp hs, hs2⟩
