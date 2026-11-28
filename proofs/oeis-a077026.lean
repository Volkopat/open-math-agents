import OMAStatements.S_oeis_a077026

open OMA.S_oeis_a077026

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a077026.main) := by
  intro h
  have h1 := h 1 le_rfl
  have hfl : ⌊(3 / 2 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    norm_num
  have ha : a 1 = 1 := by
    simp only [a, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
    rw [show (1 : ℝ) + 1 = ((2 : ℤ) : ℝ) by norm_num, Int.floor_intCast,
      show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, hfl]
    norm_num
  rw [ha] at h1
  simp at h1
