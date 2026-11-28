import OMAStatements.S_oeis_a362534

-- Disproof: at n = 19, g 19 = 215955/2^17 but f 19 / g 19 = 92378/43191, so num (g 19) ≠ den (f/g).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a362534.main) := by
  intro h
  have h19 := h 19 (by norm_num)
  have e1 : OMA.S_oeis_a362534.g 19 = ((215955 : ℤ) : ℚ) / ((131072 : ℤ) : ℚ) := by
    simp only [OMA.S_oeis_a362534.g]; norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  have e2 : OMA.S_oeis_a362534.f 19 / OMA.S_oeis_a362534.g 19 =
      ((92378 : ℤ) : ℚ) / ((43191 : ℤ) : ℚ) := by
    rw [e1]; simp only [OMA.S_oeis_a362534.f]; norm_num [Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  rw [e2, e1, Rat.num_div_eq_of_coprime (by norm_num) (by norm_num),
    Rat.den_div_eq_of_coprime (by norm_num) (by norm_num)] at h19
  norm_num at h19

