import OMAStatements.S_oeis_a351933
import Mathlib

namespace OMA.A351933

open PowerSeries OMA.S_oeis_a351933

private noncomputable def D := PowerSeries.derivative ℚ

/-- Multiplying by the denominator clears the derivative of the rational argument. -/
private theorem argument_derivative :
    denominator^2 * D argument = 4 + 2 * X^2 := by
  have two : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
  have nonzero : constantCoeff denominator ≠ 0 := by
    unfold denominator
    rw [← two, map_sub, map_pow]
    norm_num
  have cancellation : denominator * argument = 2*X := by
    unfold argument
    calc
      denominator * (2*X*denominator⁻¹) = 2*X*(denominator*denominator⁻¹) := by ring
      _ = 2*X := by rw [PowerSeries.mul_inv_cancel _ nonzero, mul_one]
  have dDen : D denominator = -(2*X) := by
    unfold denominator D
    rw [map_sub, ← two, derivative_C, derivative_pow]
    simp [two]
  have dTwoX : D (2*X) = 2 := by
    unfold D
    rw [← two]
    simp [Derivation.leibniz, smul_eq_mul]
  have h := congrArg (fun f => D f) cancellation
  change D (denominator * argument) = D (2*X) at h
  rw [dTwoX] at h
  have product : D (denominator * argument) =
      denominator * D argument + argument * D denominator := by
    simp [D, Derivation.leibniz, smul_eq_mul]
  rw [product] at h
  have isolate : denominator * D argument = 2 - argument * D denominator :=
    eq_sub_of_add_eq h
  calc
    denominator^2 * D argument = denominator * (denominator * D argument) := by ring
    _ = 2*denominator - (denominator*argument)*D denominator := by rw [isolate]; ring
    _ = 4+2*X^2 := by rw [cancellation, dDen]; unfold denominator; ring

/-- The differential equation for the exponential series has polynomial coefficients. -/
private theorem series_derivative :
    denominator^2 * D series = (4 + 2 * X^2) * series := by
  have inner : HasSubst argument := HasSubst.of_constantCoeff_zero (by
    have zeroX : MvPowerSeries.constantCoeff (X : PowerSeries ℚ) = 0 := constantCoeff_X
    unfold argument
    rw [map_mul, map_mul, zeroX, mul_zero, zero_mul])
  have chain : D series = series * D argument := by
    unfold D series
    rw [derivative_subst inner, derivative_exp]
  calc
    denominator^2 * D series = (denominator^2 * D argument) * series := by rw [chain]; ring
    _ = (4 + 2*X^2) * series := by rw [argument_derivative]

private noncomputable def c (n : ℕ) := coeff n series

private theorem coeff_balance (k : ℕ) :
    4*(k+4 : ℚ)*c (k+4) - 4*(k+2 : ℚ)*c (k+2) +
      (k : ℚ)*c k - 4*c (k+3) - 2*c (k+1) = 0 := by
  have expanded :
      C (4 : ℚ) * D series - C (4 : ℚ) * (D series * X^2) + D series * X^4 =
        C (4 : ℚ) * series + C (2 : ℚ) * (series * X^2) := by
    calc
      _ = denominator^2 * D series := by
        rw [show C (4 : ℚ) = (4 : PowerSeries ℚ) from map_ofNat C 4]
        unfold denominator
        ring
      _ = (4 + 2*X^2)*series := series_derivative
      _ = _ := by
        rw [show C (4 : ℚ) = (4 : PowerSeries ℚ) from map_ofNat C 4,
          show C (2 : ℚ) = (2 : PowerSeries ℚ) from map_ofNat C 2]
        ring
  have fourthShift : coeff (k+3) (D series * X^4) = c k * k := by
    rw [coeff_mul_X_pow']
    cases k with
    | zero => norm_num
    | succ k =>
      rw [if_pos (by omega)]
      unfold D c
      rw [show (k+1)+3-4 = k by omega, coeff_derivative]
      push_cast
      rfl
  have h := congrArg (fun f : PowerSeries ℚ => coeff (k+3) f) expanded
  simp only [map_add, map_sub, coeff_C_mul, fourthShift, coeff_mul_X_pow',
    if_pos (show 2 ≤ k+3 by omega), show k+3-2 = k+1 by omega] at h
  unfold D at h
  simp only [coeff_derivative, Nat.cast_add, Nat.cast_ofNat,
    show k+3+1 = k+4 by omega, show k+1+1 = k+2 by omega] at h
  simp only [c] at h ⊢
  linear_combination h

private def fac (n : ℕ) : ℚ := n.factorial

private theorem fac_succ (n : ℕ) : fac (n+1) = (n+1 : ℚ) * fac n := by
  unfold fac
  rw [Nat.factorial_succ, Nat.cast_mul]
  push_cast
  rfl

private theorem recurrence (k : ℕ) :
    4*a (k+4) - 4*a (k+3) - 4*(k+3 : ℚ)*(k+2 : ℚ)*a (k+2) -
      2*(k+3 : ℚ)*(k+2 : ℚ)*a (k+1) +
      (k+3 : ℚ)*(k+2 : ℚ)*(k+1 : ℚ)*k*a k = 0 := by
  have h := congrArg (fun x : ℚ => fac (k+3)*x) (coeff_balance k)
  simp only [mul_zero] at h
  have definition (n : ℕ) : a n = fac n * c n := rfl
  simp only [definition]
  rw [show k+4 = (k+3)+1 by omega, fac_succ (k+3),
    show k+3 = (k+2)+1 by omega, fac_succ (k+2),
    show k+2 = (k+1)+1 by omega, fac_succ (k+1), fac_succ k]
  rw [show k+3 = (k+2)+1 by omega, fac_succ (k+2),
    show k+2 = (k+1)+1 by omega, fac_succ (k+1), fac_succ k] at h
  push_cast at h ⊢
  linear_combination h

end OMA.A351933

open OMA.S_oeis_a351933 in
theorem OMA.solution : type_of% @OMA.S_oeis_a351933.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4, by omega⟩
  rw [show k+4-1 = k+3 by omega, show k+4-2 = k+2 by omega,
    show k+4-3 = k+1 by omega, show k+4-4 = k by omega]
  push_cast
  linear_combination OMA.A351933.recurrence k