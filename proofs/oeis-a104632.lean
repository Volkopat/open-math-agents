import OMAStatements.S_oeis_a104632

/-! The pentanomial is reciprocal, so the two coefficients adjacent to the center
are equal. After combining them, Mathar's recurrence is the coefficient of
`X * derivative E - (2k+7) * E` in degree `2k+7` for the explicit polynomial
`E` below. This coefficient vanishes for every polynomial. -/

namespace OMA.S_oeis_a104632
open Polynomial

private noncomputable def b (n : ℕ) : ℚ := (pentanomial^n).coeff (2*n+1)

private lemma reflect_pentanomial : reflect 4 pentanomial = pentanomial := by
  have hx := reflect_monomial (R:=ℚ) 4 1
  simp only [pow_one] at hx
  rw [pentanomial]
  simp only [reflect_add, reflect_monomial, hx, reflect_one]
  rw [show revAt 4 1 = 3 by decide, show revAt 4 2 = 2 by decide,
    show revAt 4 3 = 1 by decide, show revAt 4 4 = 0 by decide]
  ring

private lemma reflect_power (n : ℕ) : reflect (4*n) (pentanomial^n) = pentanomial^n := by
  have hd : pentanomial.natDegree ≤ 4 := by unfold pentanomial; compute_degree
  induction n with
  | zero => simp [reflect_one]
  | succ n ih =>
    rw [Nat.mul_succ, pow_succ, reflect_mul, ih, reflect_pentanomial]
    · rw [natDegree_pow, mul_comm 4 n]
      exact Nat.mul_le_mul_left n hd
    · exact hd

private noncomputable def paired (n : ℕ) : ℚ[X] := (1+X^2)*pentanomial^n

private lemma coeff_paired (n : ℕ) : (paired n).coeff (2*n+1) = 2*b n := by
  cases n with
  | zero => norm_num [paired, b, coeff_X_pow, coeff_one]
  | succ n =>
    have hr := congrArg (fun p : ℚ[X] => p.coeff (2*(n+1)+1)) (reflect_power (n+1))
    change (reflect _ _).coeff _ = _ at hr
    rw [coeff_reflect, revAt_le (by omega), show 4*(n+1)-(2*(n+1)+1) = 2*n+1 by omega] at hr
    rw [paired, add_mul, one_mul, coeff_add, coeff_X_pow_mul', if_pos (by omega),
      show 2*(n+1)+1-2 = 2*n+1 by omega, hr, b]
    ring

/-- A polynomial whose derivative certifies the recurrence after coefficient extraction. -/
private noncomputable def cert (k : ℕ) : ℚ[X] :=
  C (2*(k:ℚ)+4) * (X^10-1) + C (5*(k:ℚ)+10) * (X^9-X)
  + C (2*(k:ℚ)+2) * (X^8-X^2) + C (7*(k:ℚ)+17) * (X^7-X^3)
  + C 5*(X^4-X^6)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private lemma polynomial_certificate (k : ℕ) :
    let E := cert k * pentanomial^(k+1)
    X * derivative E - C (2*(k:ℚ)+7)*E =
      C (2*(2*((k:ℚ)+3)+1)*((k:ℚ)+2)) * paired (k+3)
      - C (19*((k:ℚ)+3)^2-19*((k:ℚ)+3)+2) * (X^2 * paired (k+2))
      - C (5*(2*((k:ℚ)+3)^2-3*((k:ℚ)+3)-1)) * (X^4 * paired (k+1))
      + C (25*((k:ℚ)+3)*((k:ℚ)+1)) * (X^6 * paired k) := by
  dsimp only
  rw [derivative_mul, derivative_pow_succ]
  simp only [paired, pow_succ pentanomial]
  generalize pentanomial^k = Y
  simp only [cert, pentanomial, derivative_add, derivative_sub, derivative_C_mul,
    derivative_X_pow, derivative_X, derivative_one]
  norm_num [map_add, map_mul, map_pow, map_sub, map_ofNat, map_natCast]
  ring

private lemma rec_b (k : ℕ) :
    2*(2*((k:ℚ)+3)+1)*((k:ℚ)+2)*b (k+3)
    - (19*((k:ℚ)+3)^2-19*((k:ℚ)+3)+2)*b (k+2)
    - 5*(2*((k:ℚ)+3)^2-3*((k:ℚ)+3)-1)*b (k+1)
    + 25*((k:ℚ)+3)*((k:ℚ)+1)*b k = 0 := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (2*k+7)) (polynomial_certificate k)
  simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul,
    coeff_X_pow_mul', if_pos (show 2 ≤ 2*k+7 by omega), if_pos (show 4 ≤ 2*k+7 by omega),
    if_pos (show 6 ≤ 2*k+7 by omega)] at h
  rw [show 2*k+7-2 = 2*(k+2)+1 by omega, show 2*k+7-4 = 2*(k+1)+1 by omega,
    show 2*k+7-6 = 2*k+1 by omega, show 2*k+7 = 2*(k+3)+1 by omega] at h
  simp only [coeff_paired] at h
  push_cast at h
  linarith only [h]

private lemma scale (n : ℕ) (h : 0<n) : b n = n * a n := by
  unfold a b
  field_simp

end OMA.S_oeis_a104632
open OMA.S_oeis_a104632

theorem OMA.solution : type_of% @OMA.S_oeis_a104632.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  have h := rec_b (k+1)
  rw [scale _ (by omega), scale _ (by omega), scale _ (by omega), scale _ (by omega)] at h
  dsimp only
  rw [show k+4-1 = k+3 by omega, show k+4-2 = k+2 by omega, show k+4-3 = k+1 by omega]
  norm_num [Nat.add_assoc] at h ⊢
  linear_combination h
