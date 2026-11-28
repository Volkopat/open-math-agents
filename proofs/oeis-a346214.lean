import OMAStatements.S_oeis_a346214
open OMA.S_oeis_a346214 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a346214.main) := by
  intro ⟨_, hfin⟩
  have h := hfin 2 1 (by decide) (by decide) (by decide)
  have ht : table 2 1 = 1 := by
    unfold table
    rw [show {M : BinaryMatrix 2 | 0 < 1 ∧ M ^ 1 = 0 ∧ ∀ i : ℕ, 0 < i → i < 1 → M ^ i ≠ 0} = {0} by
      ext; simp; omega, Set.ncard_singleton]
  rw [show (2 : ℕ) - 1 = 1 by rfl, ht, show glOrder 1 = 1 by decide,
    show glOrder 2 = 6 by decide] at h
  exact absurd h (by decide)
