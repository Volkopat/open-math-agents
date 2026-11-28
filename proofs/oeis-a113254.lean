import OMAStatements.S_oeis_a113254

open OMA.S_oeis_a113254

theorem OMA.solution : type_of% @OMA.S_oeis_a113254.main := by
  intro m n
  suffices h : ∃ x y : ℤ, a m (2 * n) = y * x + (m : ℤ) ^ (2 * n) ∧ a m (2 * n + 1) = y * y ∧
      a m (2 * n + 2) = (-4 * y - (m : ℤ) ^ 2 * x) * y + (m : ℤ) ^ (2 * n + 2) ∧
      a m (2 * n + 3) = (-4 * y - (m : ℤ) ^ 2 * x) ^ 2 from
    let ⟨_, y, _, h, _⟩ := h; ⟨y, h⟩
  induction n with
  | zero => refine ⟨-1, 2, ?_, ?_, ?_, ?_⟩ <;> norm_num [a] <;> ring
  | succ n ih =>
    obtain ⟨x, y, h0, h1, h2, h3⟩ := ih
    refine ⟨y, -4 * y - (m : ℤ) ^ 2 * x, h2, h3.trans (sq _), ?_, ?_⟩
    · rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring, a, h0, h1, h3]
      ring
    · rw [show 2 * (n + 1) + 3 = 2 * n + 1 + 4 by ring, a, show 2 * n + 1 + 3 = 2 * n + 4 by ring, a,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, h0, h1, h2, h3]
      ring
