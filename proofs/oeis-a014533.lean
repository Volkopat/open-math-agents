import OMAStatements.S_oeis_a014533

open Polynomial OMA.S_oeis_a014533
noncomputable section

private abbrev T : ℤ[X] := 1 + X + X^2

private def E (p : ℤ[X]) := X * derivative p

private lemma coeff_E (p : ℤ[X]) (s : ℕ) :
    (E p).coeff (s+1) = (s+1 : ℤ) * p.coeff (s+1) := by
  simp [E, coeff_X_mul, coeff_derivative, mul_comm]

private lemma ode (r : ℕ) :
    E (E (T^(r+2))) - C (2*(r+2 : ℤ)) * E (T^(r+2)) +
      C ((r+2 : ℤ)*(2*r+3)) * (X * T^(r+1)) +
      C (3*(r+2 : ℤ)*(r+1)) * (X * (X * T^r)) = 0 := by
  have dt : derivative T = 1 + 2*X := by simp [T, derivative_pow]
  have d2 : derivative (1 + 2*X : ℤ[X]) = 2 := by simp
  simp only [E, show r+2 = (r+1)+1 from rfl, derivative_pow_succ, dt, derivative_mul,
    derivative_C, derivative_X, d2, derivative_one, zero_mul, zero_add, one_mul, Nat.cast_succ,
    map_add, map_mul, map_ofNat, map_one]
  rw [pow_succ T r]
  generalize T^r = p
  unfold T
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a014533.main := by
  intro n hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [show n = k+2 by omega]
  rw [show k+2-1 = k+1 by omega, show k+2-2 = k by omega]
  have h := congrArg (fun p : ℤ[X] => p.coeff (k+9)) (ode (k+3))
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_E, coeff_zero,
    Nat.cast_add, Nat.cast_ofNat] at h
  simp only [aSeq, Nat.cast_add, Nat.cast_ofNat]
  linear_combination h
