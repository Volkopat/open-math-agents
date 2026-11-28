import OMAStatements.S_oeis_a005517

/-!
Compare coefficients. After `coeff_mul_X_pow'`, the coefficient `m` of the left side is
`a(m+1) - 5 a(m-2)` for `m ≥ 3` and `a(m+1)` below. The first five cases are numeric; for
`m ≥ 5` the closed form of `a` gives `a(m+1) = 5 a(m-2)` in each residue class mod 3.
-/

open OMA.S_oeis_a005517 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a005517.main := by
  ext m
  rw [show (5 : PowerSeries ℚ) = C 5 from rfl, show (2 : PowerSeries ℚ) = C 2 from rfl,
    show (3 : PowerSeries ℚ) = C 3 from rfl, mul_sub, mul_one, map_sub, mul_left_comm,
    coeff_C_mul, coeff_mul_X_pow']
  obtain _|_|_|_|_|k := m <;> norm_num [coeff_X_pow, coeff_X, coeff_one, A005517]
  split_ifs <;> (try omega) <;> simp [sub_eq_zero, mul_left_comm (5 : ℚ), ← pow_succ'] <;> omega
