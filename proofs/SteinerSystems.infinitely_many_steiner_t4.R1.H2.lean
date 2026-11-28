import OMAReductions.R_SteinerSystems_infinitely_many_steiner_t4_R1

theorem OMA.solution : OMA.R_SteinerSystems_infinitely_many_steiner_t4_R1.H2 := fun N =>
  ⟨120 * N + 5, by omega, fun i hi => Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos (4 - i)) (by
    simp only [← Nat.descFactorial_eq_factorial_mul_choose]
    interval_cases i <;> exact Nat.dvd_of_mod_eq_zero (by simp [Nat.descFactorial, Nat.mul_mod, Nat.add_mod]))⟩
