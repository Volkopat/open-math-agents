import OMAStatements.S_oeis_a192357

open Polynomial OMA.S_oeis_a192357

theorem OMA.solution : type_of% @OMA.S_oeis_a192357.main := by
  rintro (_|_|_|_|_|k) _ <;> try omega
  have h n : a n = lcoeff ℚ 0 (modByMonicHom _ (p (n - 1))) := rfl
  simp only [h, ← smul_eq_mul, ← map_smul, ← map_add, ← map_sub]
  congr 1
  exact modByMonic_eq_of_dvd_sub (by monicity!)
    ⟨C (1 / 2) * ((X + 3) ^ k * (X ^ 2 + 11 * X + 29) + (X - 3) ^ k * (X ^ 2 - 13 * X + 41)), by
      simp [p, smul_eq_C_mul, map_ofNat]; ring⟩
