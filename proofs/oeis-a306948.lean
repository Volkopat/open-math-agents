import OMAStatements.S_oeis_a306948

open PowerSeries OMA.S_oeis_a306948

private lemma ode : (1 + X) * d⁄dX ℚ egf - egf - egf - egf * X = exp ℚ + exp ℚ * X := by
  have h : (1 + X) * d⁄dX ℚ (log ℚ) = 1 := by
    ext (_ | n) <;> simp [deriv_log, add_mul, coeff_succ_X_mul, pow_succ]
  simp only [egf, Derivation.leibniz, derivative_exp, map_add, derivative_X,
    Derivation.map_one_eq_zero, smul_eq_mul]
  linear_combination (1 + X) * exp ℚ * h

private lemma rec1 (m : ℕ) :
    a (m + 2) + ((m : ℚ) - 1) * a (m + 1) - ((m : ℚ) + 1) * a m = (m : ℚ) + 2 := by
  have h := congrArg (coeff (m + 1)) ode
  simp only [map_add, map_sub, add_mul, one_mul, coeff_succ_X_mul, coeff_succ_mul_X,
    coeff_derivative, coeff_exp] at h
  have e1 : ((m : ℚ) + 1) * m.factorial * (1 / ((m + 1) * m.factorial)) = 1 :=
    mul_one_div_cancel (by positivity)
  have e2 : (m.factorial : ℚ) * (1 / m.factorial) = 1 := mul_one_div_cancel (by positivity)
  simp only [a, Nat.factorial_succ] at h ⊢
  push_cast at h ⊢
  linear_combination (m + 1) * (m.factorial : ℚ) * h + e1 + (m + 1) * e2

theorem OMA.solution : type_of% @OMA.S_oeis_a306948.main := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h0 := rec1 r
  have h1 := rec1 (r + 1)
  have h2 := rec1 (r + 2)
  push_cast at h0 h1 h2 ⊢
  linear_combination h2 - 2 * h1 + h0
