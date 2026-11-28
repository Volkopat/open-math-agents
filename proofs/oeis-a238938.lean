import OMAStatements.S_oeis_a238938

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a238938.main) := by
  intro h
  have hm : (4722366482869645213696 : ℕ) ∈
      {m : ℕ | (∃ e : ℕ, m = 2 ^ e) ∧ 0 ∉ Nat.digits 10 m} := by
    constructor
    · exact ⟨72, by decide +kernel⟩
    · decide +kernel
  rw [h] at hm
  revert hm
  decide +kernel
