import OMAStatements.S_oeis_a026672

/-! The root equation and the generating-function relation give polynomial
certificates for the Euler derivatives. Taking coefficients yields the recurrence. -/

open PowerSeries
open scoped PowerSeries

namespace SqrtRecurrence_oeis_a026672

private noncomputable abbrev XX : PowerSeries ℚ := X

private noncomputable def euler (f : PowerSeries ℚ) : PowerSeries ℚ :=
  XX * derivative ℚ f

private theorem derivativeMul (f g : PowerSeries ℚ) :
    derivative ℚ (f*g) = f*derivative ℚ g + g*derivative ℚ f := by
  simpa only [smul_eq_mul] using (PowerSeries.derivative ℚ).leibniz f g

private theorem eulerMul (f g : PowerSeries ℚ) :
    euler (f*g) = f*euler g + g*euler f := by
  rw [euler, derivativeMul]
  simp only [euler]
  ring

private theorem eulerAdd (f g : PowerSeries ℚ) :
    euler (f+g) = euler f + euler g := by
  simp [euler, mul_add]

private theorem squareEuler {S P : PowerSeries ℚ} (h : S^2 = P) :
    2*P*euler S = euler P*S := by
  have hd := congrArg euler h
  rw [pow_two, eulerMul S S] at hd
  linear_combination S*hd - 2*euler S*h

private theorem coeffEuler (f : PowerSeries ℚ) (j : ℕ) :
    coeff j (euler f) = (j : ℚ) * coeff j f := by
  cases j with
  | zero => simp [euler]
  | succ j =>
    rw [euler, coeff_succ_X_mul, coeff_derivative]
    simp [mul_comm]

private noncomputable def term (a : ℚ) (j : ℕ) : PowerSeries ℚ := C a * XX^j

private theorem coeffTerm (a : ℚ) (j k : ℕ) :
    coeff k (term a j) = if k = j then a else 0 :=
  coeff_C_mul_X_pow a j k

private theorem coeffTermMul (a : ℚ) (j k : ℕ) (f : PowerSeries ℚ) :
    coeff k (term a j * f) = a * (if j ≤ k then coeff (k-j) f else 0) := by
  rw [term, mul_assoc, coeff_C_mul, coeff_X_pow_mul']

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 10000 in
theorem checked : type_of% @OMA.S_oeis_a026672.main := by

  intro S c G hSquare _ hAux hInput n hn
  let Y : PowerSeries ℚ := (1)*S
  have hYLink : (1)*S - Y = 0 := by simp [Y]
  have hY : Y^2 = (1 - 4*XX) := by
    dsimp only [Y]
    linear_combination (1)*hSquare
  have hNoAux : (-XX + 4*XX*S - 6*XX*S^2 + 4*XX*S^3 - XX*S^4 - 2*XX^2*G + 6*XX^2*S*G - 6*XX^2*S^2*G + 2*XX^2*S^3*G + 16*XX^4*G) = 0 := by
    linear_combination (16*XX^4)*hInput - (-XX + 3*XX*S - 3*XX*S^2 + XX*S^3 - 2*XX^2*c - 2*XX^2*G + 4*XX^2*S*c + 4*XX^2*S*G - 2*XX^2*S^2*c - 2*XX^2*S^2*G - 4*XX^3*c^2 - 4*XX^3*G*c + 4*XX^3*S*c^2 + 4*XX^3*S*G*c - 8*XX^4*c^3 - 8*XX^4*G*c^2)*hAux
  have hNoRoot : (-XX + 4*XX*Y - 6*XX*Y^2 + 4*XX*Y^3 - XX*Y^4 - 2*XX^2*G + 6*XX^2*Y*G - 6*XX^2*Y^2*G + 2*XX^2*Y^3*G + 16*XX^4*G) = 0 := by
    linear_combination (1)*hNoAux - (4*XX - 6*XX*Y + 4*XX*Y^2 - XX*Y^3 - 6*XX*S + 4*XX*S*Y - XX*S*Y^2 + 4*XX*S^2 - XX*S^2*Y - XX*S^3 + 6*XX^2*G - 6*XX^2*Y*G + 2*XX^2*Y^2*G - 6*XX^2*S*G + 2*XX^2*S*Y*G + 2*XX^2*S^2*G)*hYLink
  have hReduced : (-8*XX + 8*XX*Y + 32*XX^2 - 8*XX^2*G - 16*XX^2*Y + 8*XX^2*Y*G - 16*XX^3 + 24*XX^3*G - 8*XX^3*Y*G + 16*XX^4*G) = 0 := by
    linear_combination hNoRoot - (-7*XX + 4*XX*Y - XX*Y^2 + 4*XX^2 - 6*XX^2*G + 2*XX^2*Y*G)*hY
  have hNonzero1 : ((128*XX^5) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 5) heq
    rw [show ((128*XX^5) : PowerSeries ℚ) = term (128) 5 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder0 : (-2*XX + 8*XX^2 + 2*XX^3)*G = (1 - 5*XX + 2*XX^2)+(-1 + 3*XX)*Y := by
    apply mul_left_cancel₀ hNonzero1
    linear_combination (-8*XX^2 - 8*XX^2*Y + 24*XX^3 + 8*XX^3*Y + 16*XX^4)*hReduced - (-64*XX^3 + 192*XX^4 - 64*XX^4*G - 128*XX^5 + 128*XX^5*G - 64*XX^6*G)*hY
  have hEuler2 : euler (1 - 4*XX) = (-4*XX) := by
    conv_lhs => rw [show (1 - 4*XX) = term (1) 0 + term (-4) 1 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hYDeriv : 2*(1 - 4*XX)*euler Y = (-4*XX)*Y := by
    have hd := squareEuler hY
    rw [hEuler2] at hd
    exact hd
  have hEuler3 : euler (-2*XX + 8*XX^2 + 2*XX^3) = (-2*XX + 16*XX^2 + 6*XX^3) := by
    conv_lhs => rw [show (-2*XX + 8*XX^2 + 2*XX^3) = term (-2) 1 + term (8) 2 + term (2) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler4 : euler (1 - 5*XX + 2*XX^2) = (-5*XX + 4*XX^2) := by
    conv_lhs => rw [show (1 - 5*XX + 2*XX^2) = term (1) 0 + term (-5) 1 + term (2) 2 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler5 : euler (-1 + 3*XX) = (3*XX) := by
    conv_lhs => rw [show (-1 + 3*XX) = term (-1) 0 + term (3) 1 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hGradient0 := congrArg euler hOrder0
  rw [eulerMul (-2*XX + 8*XX^2 + 2*XX^3) (G), eulerAdd (1 - 5*XX + 2*XX^2) ((-1 + 3*XX)*Y),
    eulerMul (-1 + 3*XX) Y] at hGradient0
  simp only [hEuler3, hEuler4, hEuler5] at hGradient0
  have hNonzero6 : ((4*XX) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 1) heq
    rw [show ((4*XX) : PowerSeries ℚ) = term (4) 1 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder1 : (2*XX - 24*XX^2 + 92*XX^3 - 96*XX^4 - 62*XX^5 - 8*XX^6)*(euler (G)) = (1 - 12*XX + 47*XX^2 - 50*XX^3 - 42*XX^4 + 8*XX^5)+(-1 + 10*XX - 27*XX^2 + 8*XX^3 + 18*XX^4)*Y := by
    apply mul_left_cancel₀ hNonzero6
    linear_combination (-4*XX + 32*XX^2 - 60*XX^3 - 16*XX^4)*hGradient0 - (-4*XX + 48*XX^2 - 116*XX^3 - 48*XX^4)*hOrder0 + (2*XX - 14*XX^2 + 22*XX^3 + 6*XX^4)*hYDeriv
  have hEuler7 : euler (2*XX - 24*XX^2 + 92*XX^3 - 96*XX^4 - 62*XX^5 - 8*XX^6) = (2*XX - 48*XX^2 + 276*XX^3 - 384*XX^4 - 310*XX^5 - 48*XX^6) := by
    conv_lhs => rw [show (2*XX - 24*XX^2 + 92*XX^3 - 96*XX^4 - 62*XX^5 - 8*XX^6) = term (2) 1 + term (-24) 2 + term (92) 3 + term (-96) 4 + term (-62) 5 + term (-8) 6 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler8 : euler (1 - 12*XX + 47*XX^2 - 50*XX^3 - 42*XX^4 + 8*XX^5) = (-12*XX + 94*XX^2 - 150*XX^3 - 168*XX^4 + 40*XX^5) := by
    conv_lhs => rw [show (1 - 12*XX + 47*XX^2 - 50*XX^3 - 42*XX^4 + 8*XX^5) = term (1) 0 + term (-12) 1 + term (47) 2 + term (-50) 3 + term (-42) 4 + term (8) 5 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler9 : euler (-1 + 10*XX - 27*XX^2 + 8*XX^3 + 18*XX^4) = (10*XX - 54*XX^2 + 24*XX^3 + 72*XX^4) := by
    conv_lhs => rw [show (-1 + 10*XX - 27*XX^2 + 8*XX^3 + 18*XX^4) = term (-1) 0 + term (10) 1 + term (-27) 2 + term (8) 3 + term (18) 4 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hGradient1 := congrArg euler hOrder1
  rw [eulerMul (2*XX - 24*XX^2 + 92*XX^3 - 96*XX^4 - 62*XX^5 - 8*XX^6) (euler (G)), eulerAdd (1 - 12*XX + 47*XX^2 - 50*XX^3 - 42*XX^4 + 8*XX^5) ((-1 + 10*XX - 27*XX^2 + 8*XX^3 + 18*XX^4)*Y),
    eulerMul (-1 + 10*XX - 27*XX^2 + 8*XX^3 + 18*XX^4) Y] at hGradient1
  simp only [hEuler7, hEuler8, hEuler9] at hGradient1
  have hNonzero10 : ((4*XX - 32*XX^2 + 60*XX^3 + 16*XX^4) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 1) heq
    rw [show ((4*XX - 32*XX^2 + 60*XX^3 + 16*XX^4) : PowerSeries ℚ) = term (4) 1 + term (-32) 2 + term (60) 3 + term (16) 4 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder2 : (2*XX - 40*XX^2 + 314*XX^3 - 1184*XX^4 + 1990*XX^5 - 584*XX^6 - 1250*XX^7 - 368*XX^8 - 32*XX^9)*(euler (euler (G))) = (-1 + 20*XX - 156*XX^2 + 592*XX^3 - 1049*XX^4 + 484*XX^5 + 398*XX^6 + 464*XX^7 - 32*XX^8)+(1 - 18*XX + 124*XX^2 - 376*XX^3 + 393*XX^4 + 78*XX^5 + 82*XX^6 - 108*XX^7)*Y := by
    apply mul_left_cancel₀ hNonzero10
    linear_combination (4*XX - 64*XX^2 + 376*XX^3 - 928*XX^4 + 644*XX^5 + 480*XX^6 + 64*XX^7)*hGradient1 - (4*XX - 112*XX^2 + 936*XX^3 - 2976*XX^4 + 2452*XX^5 + 2384*XX^6 + 384*XX^7)*hOrder1 + (-2*XX + 44*XX^2 - 386*XX^3 + 1680*XX^4 - 3538*XX^5 + 2284*XX^6 + 2482*XX^7 - 2008*XX^8 - 1180*XX^9 - 144*XX^10)*hYDeriv
  have hNonzero11 : ((-2*XX + 40*XX^2 - 314*XX^3 + 1184*XX^4 - 1990*XX^5 + 584*XX^6 + 1250*XX^7 + 368*XX^8 + 32*XX^9) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 1) heq
    rw [show ((-2*XX + 40*XX^2 - 314*XX^3 + 1184*XX^4 - 1990*XX^5 + 584*XX^6 + 1250*XX^7 + 368*XX^8 + 32*XX^9) : PowerSeries ℚ) = term (-2) 1 + term (40) 2 + term (-314) 3 + term (1184) 4 + term (-1990) 5 + term (584) 6 + term (1250) 7 + term (368) 8 + term (32) 9 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hFinal : term (6) 0 * (G) + term (-32) 1 * (G) + term (12) 2 * (G) + term (12) 3 * (G) + term (5) 0 * (euler (G)) + term (-30) 1 * (euler (G)) + term (39) 2 * (euler (G)) + term (2) 3 * (euler (G)) + term (-1) 0 * (euler (euler (G))) + term (8) 1 * (euler (euler (G))) + term (-15) 2 * (euler (euler (G))) + term (-4) 3 * (euler (euler (G))) = term (10) 1 + term (6) 2 := by
    apply mul_left_cancel₀ hNonzero11
    simp only [term, map_ofNat, map_neg, map_one, map_zero]
    linear_combination (6 - 128*XX + 1088*XX^2 - 4580*XX^3 + 9326*XX^4 - 6088*XX^5 - 4596*XX^6 + 2860*XX^7 + 1632*XX^8 + 192*XX^9)*hOrder0 + (-5 + 70*XX - 354*XX^2 + 740*XX^3 - 449*XX^4 - 186*XX^5 - 8*XX^6)*hOrder1 + (1 - 8*XX + 15*XX^2 + 4*XX^3)*hOrder2
  have hnCoeff := congrArg (coeff n) hFinal
  have hLag0 : 0 ≤ n := by omega
  have hLag1 : 1 ≤ n := by omega
  have hLag2 : 2 ≤ n := by omega
  have hLag3 : 3 ≤ n := by omega
  have hRhs1 : n ≠ 1 := by omega
  have hRhs2 : n ≠ 2 := by omega
  simp only [map_add, map_zero, coeffTermMul, coeffTerm, coeffEuler, if_true, if_false, Nat.sub_zero, hLag0, hLag1, hLag2, hLag3, hRhs1, hRhs2, Nat.cast_sub hLag1, Nat.cast_sub hLag2, Nat.cast_sub hLag3, Nat.cast_ofNat] at hnCoeff
  linear_combination ((1 : ℚ))*hnCoeff

end SqrtRecurrence_oeis_a026672

theorem OMA.solution : type_of% @OMA.S_oeis_a026672.main :=
  SqrtRecurrence_oeis_a026672.checked
