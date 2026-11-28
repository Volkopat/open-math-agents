import OMAStatements.S_oeis_a038867

/-! Every term is 2 modulo 3, while squares are 0 or 1 modulo 3.
The original project proof was merged in PR 7403 and first shortened in PR 7840. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a038867.main := by
  intro n ⟨m, hm⟩
  change (n + 5) ^ 3 - n ^ 3 = m * m at hm
  have e : (n + 5) ^ 3 = 3 * (5 * n ^ 2 + 25 * n + 41) + 2 + n ^ 3 := by grind
  rw [e, Nat.add_sub_cancel] at hm
  have h := congrArg (· % 3) hm
  rw [Nat.mul_mod m m] at h
  have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with r | r | r <;> rw [r] at h <;> omega
