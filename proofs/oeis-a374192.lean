import OMAStatements.S_oeis_a374192

open OMA.S_oeis_a374192

lemma OMA.a374192_contract (n : ℕ) (hn : 3 < n) :
    ∃ k, 0 < (step^[k]) n ∧ (step^[k]) n < n := by
  by_cases even : n % 2 = 0
  · refine ⟨1, ?_⟩
    simp [step, even]
    omega
  by_cases triple : n % 3 = 0
  · have next_even : (3 * n + 1) % 2 = 0 := by omega
    by_cases quarter : n % 4 = 1
    · have half_even : ((3 * n + 1) / 2) % 2 = 0 := by omega
      refine ⟨3, ?_⟩
      simp [Function.iterate_succ_apply', step, even, triple, next_even, half_even]
      omega
    · have half_odd : ((3 * n + 1) / 2) % 2 ≠ 0 := by omega
      have half_not_triple : ((3 * n + 1) / 2) % 3 ≠ 0 := by omega
      have succ_even : ((3 * n + 1) / 2 + 1) % 2 = 0 := by omega
      refine ⟨4, ?_⟩
      simp [Function.iterate_succ_apply', step, even, triple, next_even, half_odd,
        half_not_triple, succ_even]
      omega
  · have succ_even : (n + 1) % 2 = 0 := by omega
    refine ⟨2, ?_⟩
    simp [Function.iterate_succ_apply', step, even, triple, succ_even]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a374192.main := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : 3 < n
    · obtain ⟨k, hp, hl⟩ := OMA.a374192_contract n h
      obtain ⟨j, hj⟩ := ih _ hl hp
      exact ⟨j + k, by rwa [Function.iterate_add_apply]⟩
    · rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl
      · exact ⟨0, Or.inl rfl⟩
      · exact ⟨1, Or.inl rfl⟩
      · exact ⟨1, Or.inr rfl⟩
