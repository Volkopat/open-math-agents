import OMAStatements.S_oeis_a213421

-- Problem oeis-a213421: a(n) = Re((2 + i + j + k)^n) has generating function (1 - 2x)/(1 - 4x + 7x^2), and
-- a(n) = A168175(n) - 2 A168175(n-1) for n >= 1, where A168175 are the coefficients of 1/(1 - 4x + 7x^2).
-- Upstream: statements/oeis-a213421.lean (declaration OMA.S_oeis_a213421.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: Q = 2 + i + j + k satisfies Q^2 = 4Q - 7 (trace 4, norm 7), so Q^(n+2) = 4 Q^(n+1) - 7 Q^n and the real
-- parts satisfy a(n+2) = 4a(n+1) - 7a(n) with a(0) = 1, a(1) = 2. Comparing coefficients gives
-- (1 - 4x + 7x^2) * A(x) = 1 - 2x. Multiplying by the inverse series B of 1 - 4x + 7x^2 gives
-- A = B * (1 - 2x), and reading off the coefficient of x^n gives the second claim.

open PowerSeries OMA.S_oeis_a213421

private lemma Q_sq_a213421 : Q * Q = (4 : ℤ) • Q - (7 : ℤ) • (1 : Quaternion ℤ) := by
  ext <;> decide +kernel

private lemma a_zero_a213421 : a 0 = 1 := by decide +kernel

private lemma a_one_a213421 : a 1 = 2 := by decide +kernel

private lemma a_rec_a213421 (n : ℕ) : a (n + 2) = 4 * a (n + 1) - 7 * a n := by
  have h : Q ^ (n + 2) = (4 : ℤ) • Q ^ (n + 1) - (7 : ℤ) • Q ^ n := by
    calc Q ^ (n + 2) = Q ^ n * (Q * Q) := by rw [pow_add, pow_two]
      _ = (4 : ℤ) • Q ^ (n + 1) - (7 : ℤ) • Q ^ n := by
        rw [Q_sq_a213421, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, pow_succ]
  exact congrArg QuaternionAlgebra.re h

private lemma gf_a213421 :
    (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) * mk a = 1 - 2 * X := by
  have key : (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) * mk a
      = mk a - C (4 : ℤ) * (X * mk a) + C (7 : ℤ) * (X ^ 2 * mk a) := by
    simp only [map_ofNat]
    ring
  have rhs : (1 - 2 * X : PowerSeries ℤ) = 1 - C (2 : ℤ) * X := by simp only [map_ofNat]
  rw [key, rhs]
  ext n
  rcases n with _ | _ | n
  · simp only [map_sub, map_add, coeff_C_mul, coeff_zero_X_mul, coeff_mk, coeff_X_pow_mul', coeff_one, coeff_X]
    norm_num [a_zero_a213421]
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_X_pow_mul', coeff_one, coeff_X]
    norm_num [a_zero_a213421, a_one_a213421]
  · have h2 : coeff (n + 1 + 1) (X ^ 2 * mk a) = a n := by
      rw [show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul, coeff_mk]
    simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_mk, h2, coeff_one, coeff_X]
    rw [show n + 1 + 1 = n + 2 from rfl, a_rec_a213421]
    simp

theorem OMA.solution : type_of% @OMA.S_oeis_a213421.main := by
  refine ⟨gf_a213421, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hB : (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ)
      * invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1 = 1 :=
    mul_invOfUnit _ 1 (by simp)
  have hA : mk a = invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1
      - C (2 : ℤ) * (X * invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1) := by
    calc mk a = ((1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ)
          * invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1) * mk a := by rw [hB, one_mul]
      _ = invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1
          * ((1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) * mk a) := by ring
      _ = invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1
          - C (2 : ℤ) * (X * invOfUnit (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) 1) := by
        rw [gf_a213421]
        simp only [map_ofNat]
        ring
  have hcoeff : a (m + 1) = coeff (m + 1) (mk a) := (coeff_mk _ _).symm
  unfold A168175
  rw [hcoeff, hA]
  simp only [map_sub, coeff_C_mul, coeff_succ_X_mul, Nat.add_sub_cancel]
