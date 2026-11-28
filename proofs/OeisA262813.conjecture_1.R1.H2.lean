import OMAReductions.R_OeisA262813_conjecture_1_R1
-- Credit: @kofls (shorter proof)
theorem OMA.solution : OMA.R_OeisA262813_conjecture_1_R1.H2 := fun n a b => by
  obtain ⟨x, -, u, -, v, -, h⟩ := (by decide +kernel : ∀ n < 90, 0 < n → ∃ x < 3, ∃ u < 24, ∃ v < 19,
    3 ≤ u ∧ 8 * n + 1 = 8 * x ^ 3 + u ^ 2 + 2 * v ^ 2) n b a
  exact ⟨x, u, v, h⟩
