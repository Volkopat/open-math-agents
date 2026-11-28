import OMAStatements.S_oeis_a085887


theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085887.main) := by
  rintro ⟨-, h2, -⟩
  have h4 : OMA.S_oeis_a085887.a 4 = 4 := h2 4 ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  have hle : OMA.S_oeis_a085887.a 4 ≤ 3 := by
    apply Nat.sInf_le
    refine ⟨1, 3, le_refl _, by norm_num, rfl, ?_⟩
    decide
  omega
