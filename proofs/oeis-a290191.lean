import OMAStatements.S_oeis_a290191

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290191.main) := by
  intro h
  obtain ⟨m, hm_eq, ha_eq⟩ := h 2
  have hm1 : (m : ℚ) = (1 : ℚ) := by
    rw [hm_eq]
    norm_num
  have hm : m = 1 := by exact_mod_cast hm1
  subst hm
  have hv2 : OMA.S_oeis_a290191.a 2 = 111 := by decide
  have ht1 : OMA.S_oeis_a290191.toBinaryDecimal 1 = 1 := by decide
  omega
