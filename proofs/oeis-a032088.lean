import OMAStatements.S_oeis_a032088

-- Problem: A032088: Number of reversible strings with n beads of 5 colors. If more than 1 bead, not palindromic.
-- Upstream: formal-conjectures statements/oeis-a032088.lean:0 (declaration OMA.S_oeis_a032088.main)
-- Credit: @EliaSupernova (the owner of the agent is credited as the solver)

open OMA.S_oeis_a032088

private theorem a_of_ge_two (n : ℕ) (hn : 2 ≤ n) :
    a n = ((5 : ℚ) ^ n - (5 : ℚ) ^ ((n + 1) / 2)) / 2 := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]

private theorem recurrence (n : ℕ) (hn : 4 < n) :
    a n = 5 * a (n - 1) + 5 * a (n - 2) - 25 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  rw [a_of_ge_two _ (by omega), a_of_ge_two _ (by omega),
    a_of_ge_two _ (by omega), a_of_ge_two _ (by omega)]
  -- Increasing the index by two increases the rounded-up half by one.
  rw [show (m + 5 + 1) / 2 = (m + 3 + 1) / 2 + 1 by omega,
    show (m + 4 + 1) / 2 = (m + 2 + 1) / 2 + 1 by omega]
  generalize (m + 3 + 1) / 2 = i
  generalize (m + 2 + 1) / 2 = j
  ring

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a032088.main := by
  refine ⟨recurrence, ?_, ?_, ?_⟩
  · have expanded : ((1 - C 5 * X) * (1 - C 5 * X ^ 2)) * series =
        series - C 5 * (X ^ 1 * series) - C 5 * (X ^ 2 * series) +
          C 25 * (X ^ 3 * series) := by
      have h25 : (C 25 : ℚ⟦X⟧) = C 5 * C 5 := by
        rw [← map_mul]
        norm_num
      rw [h25]
      ring
    rw [expanded]
    ext n
    unfold series
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_X]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> norm_num [a]
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), recurrence n (by omega)]
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, if_false]
      ring
  · intro n hn he
    have half : (n + 1) / 2 = n / 2 := by
      obtain ⟨k, rfl⟩ := he
      omega
    have whole : (5 : ℚ) ^ n = (5 : ℚ) ^ (n / 2) * (5 : ℚ) ^ (n / 2) := by
      rw [← pow_add]
      congr 1
      obtain ⟨k, rfl⟩ := he
      omega
    rw [a_of_ge_two n (by omega), half, whole]
    ring
  · intro n hn ho
    have half : (n + 1) / 2 = (n - 1) / 2 + 1 := by
      obtain ⟨k, rfl⟩ := ho
      omega
    have whole : (5 : ℚ) ^ n = (5 : ℚ) ^ (n - 1) * 5 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [a_of_ge_two n (by omega), half, whole, pow_succ]
    ring

