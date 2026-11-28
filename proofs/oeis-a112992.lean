import OMAStatements.S_oeis_a112992

open OMA.S_oeis_a112992 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112992.main := by
  have P (m : ℕ) : 3 * (J m : ℤ) + (-1) ^ m = 2 ^ m ∧ J m % 2 = if m = 0 then 0 else 1 := by
    induction m using Nat.strong_induction_on with | _ m ih =>
    match m with
    | 0 => simp [J]
    | 1 => norm_num [J]
    | n + 2 =>
      obtain ⟨a1, b1⟩ := ih (n + 1) (by omega)
      obtain ⟨a0, -⟩ := ih n (by omega)
      simp only [J] at *
      push_cast
      exact ⟨by linear_combination a1 + 2 * a0, by simp at b1 ⊢; omega⟩
  intro k _
  simp only [c]
  generalize 2 ^ k % k = m
  obtain ⟨h, h2⟩ := P m
  have hq : (2 : ℚ) ^ m = 3 * J m + (-1) ^ m := by exact_mod_cast h.symm
  rcases Nat.even_or_odd m with e | e <;> rw [e.neg_one_pow] at hq
  · rw [show ⌈(2 : ℚ) ^ m / 3⌉ = J m + 1 by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith]
    rcases m with _ | m
    · simpa [J] using ⟨1, by simp [J]⟩
    simp at h2
    refine ⟨fun o => absurd o ?_, fun _ => ⟨_, rfl⟩⟩
    rw [Int.not_odd_iff_even, Int.even_iff]; omega
  · rw [show ⌈(2 : ℚ) ^ m / 3⌉ = J m by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith]
    simp [show m ≠ 0 by rintro rfl; simp at e] at h2
    refine ⟨fun _ => ⟨_, rfl⟩, fun o => absurd o ?_⟩
    rw [Int.not_even_iff_odd, Int.odd_iff]; omega
