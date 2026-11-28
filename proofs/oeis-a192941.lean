import OMAStatements.S_oeis_a192941

open Polynomial OMA.S_oeis_a192941

theorem OMA.solution : type_of% @OMA.S_oeis_a192941.main := by
  rintro (_|_|k) _ <;> try omega
  have h n : a n = lcoeff ℤ 0 (modByMonicHom _ (p n)) := rfl
  simp only [h, ← smul_eq_mul, ← map_smul, ← map_add]
  convert map_zero (lcoeff ℤ 0) using 2
  exact (modByMonic_eq_zero_iff_dvd (by monicity!)).2
    ⟨4 * p k, by simp [p, Finset.prod_Icc_succ_top, smul_eq_C_mul]; ring⟩
