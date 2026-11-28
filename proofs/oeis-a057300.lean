import OMAStatements.S_oeis_a057300

open OMA.S_oeis_a057300 in
theorem OMA.solution : type_of% @OMA.S_oeis_a057300.main := by
  have u (m r : ℕ) (h : r < 4) : a (4 * m + r) = 4 * a m + swapDigit r := by
    rw [a]
    split_ifs with c
    · obtain ⟨rfl, rfl⟩ : m = 0 ∧ r = 0 := by omega
      simp [swapDigit]
      rw [a]
      simp
    · rw [show (4 * m + r) / 4 = m by omega, show (4 * m + r) % 4 = r by omega]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨m, e, he, rfl⟩ : ∃ m e, e < 2 ∧ n = 2 * m + e := ⟨n / 2, n % 2, by omega, by omega⟩
  have h1 := u m (2 * e) (by omega)
  have h2 := u m (2 * e + 1) (by omega)
  rw [show 4 * m + 2 * e = 2 * (2 * m + e) by ring] at h1
  rw [show 4 * m + (2 * e + 1) = 2 * (2 * m + e) + 1 by ring] at h2
  rcases (by omega : m < 2 * m + e ∨ m = 0 ∧ e = 0) with c | ⟨rfl, rfl⟩
  · have := ih m c
    interval_cases e <;> simp only [swapDigit] at h1 h2 <;> norm_num at h1 h2 ⊢ <;> omega
  · simp [swapDigit] at h1 h2 ⊢
    omega
