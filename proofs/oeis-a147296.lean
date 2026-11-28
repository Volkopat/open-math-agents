import OMAStatements.S_oeis_a147296

theorem OMA.solution : type_of% @OMA.S_oeis_a147296.main := by
  intro n
  have h : (1 : ℚ) / 9 - 1 / ((3 * (9 * n + 1) : ℕ) : ℚ) ^ 2 =
      ((n * (9 * n + 2) : ℤ) : ℚ) / ((9 * n + 1) ^ 2 : ℤ) := by push_cast; field_simp; ring
  rw [OMA.S_oeis_a147296.a, OMA.S_oeis_a147296.A144454, OMA.S_oeis_a147296.A061039, h]
  exact Rat.num_div_eq_of_coprime (by positivity)
    (Int.isCoprime_iff_gcd_eq_one.mp (.pow_right (.mul_left ⟨-9, 1, by ring⟩ ⟨1, -1, by ring⟩)))
