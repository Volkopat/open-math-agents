import OMAStatements.S_oeis_a005043

namespace OMA.RiordanTrinomial

open Polynomial OMA.S_oeis_a005043

private noncomputable def Q : ℤ[X] := 1 + X + X ^ 2

private noncomputable def c (n k : ℕ) : ℤ := (Q ^ n).coeff k

private theorem step (n k : ℕ) :
    c (n + 1) (k + 2) = c n (k + 2) + c n (k + 1) + c n k := by
  unfold c
  rw [pow_succ', Q, add_mul, add_mul, one_mul, coeff_add, coeff_add]
  rw [show k + 2 = k + 1 + 1 by omega, coeff_X_mul,
    show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul]

private theorem q_derivative : Q.derivative = 1 + C 2 * X := by
  unfold Q
  simp [derivative_pow]

private theorem differential (n : ℕ) :
    Q * (Q ^ n).derivative = C (n : ℤ) * (Q ^ n + X * (C 2 * Q ^ n)) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow_succ, q_derivative, pow_succ]
    push_cast
    ring

/-- The coefficient of degree (k+1) in the differential identity. -/
private theorem neighboring (n k : ℕ) :
    c n (k + 2) * ((k : ℤ) + 2) + c n (k + 1) * ((k : ℤ) + 1) + c n k * k =
      (n : ℤ) * (c n (k + 1) + 2 * c n k) := by
  have hx : (X ^ 2 * (Q ^ n).derivative).coeff (k + 1) = c n k * k := by
    cases k with
    | zero => rw [coeff_X_pow_mul']; norm_num
    | succ k => rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul, coeff_derivative]; rfl
  have h := congrArg (fun P : ℤ[X] => P.coeff (k + 1)) (differential n)
  change ((1 + X + X ^ 2) * (Q ^ n).derivative).coeff (k + 1) =
    (C (n : ℤ) * (Q ^ n + X * (C 2 * Q ^ n))).coeff (k + 1) at h
  rw [add_mul, add_mul, one_mul, coeff_add, coeff_add, coeff_X_mul, hx,
    coeff_C_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative, coeff_derivative] at h
  push_cast at h
  exact h

private theorem central_symmetry (n : ℕ) :
    c (n + 1) (n + 2) = c (n + 1) n := by
  have h := neighboring (n + 1) n
  push_cast at h
  have hz : ((n : ℤ) + 2) * (c (n + 1) (n + 2) - c (n + 1) n) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hz with hm | hm
  · omega
  · exact sub_eq_zero.mp hm

private noncomputable def R (n : ℕ) : ℤ := c n n - c n (n + 1)

private theorem step_R (n : ℕ) : R (n + 1) = c n (n + 1) - c n (n + 2) := by
  cases n with
  | zero => norm_num [R, c, Q, coeff_add, coeff_X, coeff_X_pow, coeff_one]
  | succ n =>
    unfold R
    change c (n + 1 + 1) (n + 2) - c (n + 1 + 1) (n + 3) = _
    rw [step (n + 1) n, step (n + 1) (n + 1), central_symmetry n]
    ring

private theorem recurrence (n : ℕ) :
    ((n : ℤ) + 3) * R (n + 2) =
      ((n : ℤ) + 1) * (2 * R (n + 1) + 3 * R n) := by
  rw [show n + 2 = (n + 1) + 1 by omega, step_R (n + 1), step_R n,
    step n n, step n (n + 1), R]
  have h₁ := neighboring n n
  have h₂ := neighboring n (n + 1)
  push_cast at h₂
  linear_combination 2 * h₁ - h₂

private theorem riordan_eq (n : ℕ) : riordan n = (R n : ℚ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [riordan, R, c, Q, coeff_add, coeff_X, coeff_X_pow, coeff_one]
  | one => norm_num [riordan, R, c, Q, coeff_add, coeff_X, coeff_X_pow, coeff_one]
  | more n h₀ h₁ =>
    rw [riordan, h₀, h₁]
    have h := congrArg (fun z : ℤ => (z : ℚ)) (recurrence n)
    push_cast at h
    have hn : (n : ℚ) + 3 ≠ 0 := by positivity
    field_simp
    linarith

theorem difference (n : ℕ) (hn : 0 < n) :
    riordan n = ((trinomialCentral n - trinomialNext n : ℤ) : ℚ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [riordan_eq, R]
  change ((c (j + 1) (j + 1) - c (j + 1) (j + 2) : ℤ) : ℚ) =
    ((c (j + 1) (j + 1) - c (j + 1) j : ℤ) : ℚ)
  rw [central_symmetry j]

end OMA.RiordanTrinomial

theorem OMA.solution : type_of% @OMA.S_oeis_a005043.main :=
  OMA.RiordanTrinomial.difference
