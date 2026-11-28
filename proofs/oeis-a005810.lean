import OMAStatements.S_oeis_a005810

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005810.main) := by
  intro h
  have h1 := h 1 (Nat.le_refl 1)
  have ha : OMA.S_oeis_a005810.a 1 = 4 := by
    simp [OMA.S_oeis_a005810.a, Nat.choose_one_right]
  have heq : OMA.S_oeis_a005810.a 1 % 1 ^ 3 = 4 % 1 ^ 3 := by
    rw [ha, Nat.one_pow, Nat.mod_one]
  exact Nat.not_prime_one (h1.mp heq)

