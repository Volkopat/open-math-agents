import OMAStatements.S_oeis_a067360

open OMA.S_oeis_a067360 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067360.main := by
  set t := Real.arctan (1 / 4)
  have q : Real.cos t ^ 2 = 16 / 17 := by rw [Real.cos_sq_arctan]; norm_num
  have hs : Real.sin t = 1 / 4 * Real.cos t := by rw [Real.sin_arctan, Real.cos_arctan]; ring
  let c (n : ℕ) : ℝ := 17 ^ n * Real.cos (2 * n * t)
  have s (n : ℕ) : a (n + 1) = 15 * a n + 8 * c n ∧ c (n + 1) = 15 * c n - 8 * a n := by
    simp only [a, c]
    push_cast
    rw [show 2 * (n + 1 : ℝ) * t = 2 * n * t + 2 * t by ring, Real.sin_add, Real.cos_add,
      Real.sin_two_mul, Real.cos_two_mul, hs]
    generalize 2 * (n : ℝ) * t = x
    exact ⟨by linear_combination 17 ^ n * (34 * Real.sin x + 17 / 2 * Real.cos x) * q,
      by linear_combination 17 ^ n * (34 * Real.cos x - 17 / 2 * Real.sin x) * q⟩
  have P (e : ℂ) (he : e ^ 2 = -1) (n : ℕ) : (15 + 8 * e) ^ n = c n + a n * e := by
    induction n with
    | zero => simp [a, c]
    | succ n ih =>
      rw [pow_succ, ih, (s n).1, (s n).2]; push_cast; linear_combination 8 * (a n : ℂ) * he
  refine ⟨fun n hn => ?_, fun n _ => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    obtain ⟨h1, h2⟩ := s m
    obtain ⟨h3, -⟩ := s (m + 1)
    simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
    linarith
  · have := P (-Complex.I) (by simp) n
    rw [mul_neg, ← sub_eq_add_neg] at this
    rw [P _ Complex.I_sq, this]
    linear_combination (a n : ℂ) * Complex.I_sq
