import OMAStatements.S_oeis_a183978

open OMA.S_oeis_a183978

theorem A183978_a_one : a 1 = 4 := by
  have hv : ∀ A, isValid 1 A := fun A =>
    ⟨subblockSum A 0 0, fun i j => by fin_cases i; fin_cases j; rfl⟩
  have h : Nat.card {A : Fin 2 → Fin 2 → Bool // isValid 1 A} = 16 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hv), Nat.card_eq_fintype_card]
    simp
  rw [a, h]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a183978.main) := by
  intro h
  have h1 := h 1 le_rfl
  rw [A183978_a_one] at h1
  have c : ⌈((1 : ℕ) : ℚ) / 2⌉₊ = 1 := by norm_num [Nat.ceil_eq_iff]
  have f : ⌊((1 : ℕ) : ℚ) / 2⌋₊ = 0 := by norm_num [Nat.floor_eq_zero]
  rw [c, f] at h1
  norm_num at h1
