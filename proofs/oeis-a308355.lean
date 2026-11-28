import OMAStatements.S_oeis_a308355

open OMA.S_oeis_a308355

private theorem common_singleton_le_one (r : List ℕ) : common [1] r ≤ 1 := by
  cases r with
  | nil => decide
  | cons a r =>
    by_cases h : a = 1
    · subst a
      simp [common]
    · simp [common, Ne.symm h]

/-- Both partitions of 2 can be arranged palindromically, but row 1 has one entry. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a308355.main) := by
  intro h
  obtain ⟨M, hM⟩ := h 1 (Nat.le_refl _)
  have heq := hM M (Nat.le_refl _)
  have hr : row 1 = [1] := by decide
  have hp : palCount 2 = 2 := by decide
  change common (row 1) (row M) = palCount 2 at heq
  rw [hr, hp] at heq
  have hb := common_singleton_le_one (row M)
  omega
