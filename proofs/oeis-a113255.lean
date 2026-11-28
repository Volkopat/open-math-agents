import OMAStatements.S_oeis_a113255

open OMA.S_oeis_a113255

theorem OMA.solution : type_of% @OMA.S_oeis_a113255.main := by
  intro m n
  suffices h : ∃ x y : ℤ, a m (2 * n) = y * x + (m : ℤ) ^ (2 * n) ∧ a m (2 * n + 1) = y * y ∧
      a m (2 * n + 2) = (-4 * y - (m : ℤ) ^ 2 * x) * y + (m : ℤ) ^ (2 * n + 2) ∧
      a m (2 * n + 3) = (-4 * y - (m : ℤ) ^ 2 * x) ^ 2 from
    let ⟨_, y, _, h, _⟩ := h; ⟨y, h⟩
  induction n with
  | zero => exact ⟨-1, 2, by norm_num [a], by norm_num [a], by norm_num [a] <;> ring,
      by norm_num [a] <;> ring⟩
  | succ n ih =>
    obtain ⟨x, y, h0, h1, h2, h3⟩ := ih
    have hA : a m (2 * n + 4) = (m : ℤ) ^ 4 * a m (2 * n) + (2 * (m : ℤ)) ^ 2 * a m (2 * n + 1) -
        4 * a m (2 * n + 3) := rfl
    have hB : a m (2 * n + 5) = (m : ℤ) ^ 4 * a m (2 * n + 1) +
        (2 * (m : ℤ)) ^ 2 * a m (2 * n + 2) - 4 * a m (2 * n + 4) := rfl
    refine ⟨y, -4 * y - (m : ℤ) ^ 2 * x, h2, h3.trans (sq _), ?_, ?_⟩
    · show a m (2 * n + 4) = _
      rw [hA, h0, h1, h3]
      ring
    · show a m (2 * n + 5) = _
      rw [hB, hA, h0, h1, h2, h3]
      ring
