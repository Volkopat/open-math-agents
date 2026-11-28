import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1_H1_R1

-- Step Arxiv.2607.27197.maxwell_conjecture.variants.three_equal_magnitudes.R1.H1.R1.H1: hypothesis H1 of reduction Arxiv.2607.27197.maxwell_conjecture.variants.three_equal_magnitudes.R1.H1.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1_H1_R1.H1 := by
  intro q u w hw hq heq p ⟨hnz, h1, h2⟩
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2
  have hn0 := hnz 0
  have hn1 := hnz 1
  have hn2 := hnz 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hn0 hn1 hn2
  rw [heq 1 0, heq 2 0] at h1 h2
  set Q := q 0 with hQ
  have hQ0 : Q ≠ 0 := hq 0
  set d0 := (p.1 - 0) ^ 2 + (p.2 - 0) ^ 2
  set d1 := (p.1 - 1) ^ 2 + (p.2 - 0) ^ 2
  set d2 := (p.1 - u) ^ 2 + (p.2 - w) ^ 2
  have pos : ∀ d : ℝ, 0 ≤ d → d ≠ 0 → 0 < Real.sqrt d ^ 3 := fun d h h' =>
    pow_pos (Real.sqrt_pos.2 (lt_of_le_of_ne h (Ne.symm h'))) 3
  have s0 := pos d0 (by positivity) hn0
  have s1 := pos d1 (by positivity) hn1
  have s2 := pos d2 (by positivity) hn2
  set a := Real.sqrt d0 ^ 3
  set b := Real.sqrt d1 ^ 3
  set c := Real.sqrt d2 ^ 3
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 / a + 1 / b + 1 / c := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  have hCne : C ≠ 0 := hCpos.ne'
  have e1 : p.1 * C = 1 / b + u / c := by
    have : Q * (p.1 * C - (1 / b + u / c)) = 0 := by
      rw [← h1, hC]; field_simp; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hQ0
    · linarith
  have e2 : p.2 * C = w / c := by
    have : Q * (p.2 * C - w / c) = 0 := by
      rw [← h2, hC]; field_simp; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hQ0
    · linarith
  refine ⟨(1 / a) / C, (1 / b) / C, (1 / c) / C, by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · rw [hC]; field_simp
  · calc p.1 = p.1 * C / C := by field_simp
      _ = _ := by rw [e1]; ring
  · calc p.2 = p.2 * C / C := by field_simp
      _ = _ := by rw [e2]; ring
