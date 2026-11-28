import OMAStatements.S_oeis_a026026

/-! The root equation and the generating-function relation give polynomial
certificates for the Euler derivatives. Taking coefficients yields the recurrence. -/

open PowerSeries
open scoped PowerSeries

namespace SqrtRecurrence_oeis_a026026

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
theorem checked : type_of% @OMA.S_oeis_a026026.main := by

  intro S c G hSquare _ hAux hInput n hn
  let Y : PowerSeries ℚ := (1)*S
  have hYLink : (1)*S - Y = 0 := by simp [Y]
  have hY : Y^2 = (1 - 4*XX) := by
    dsimp only [Y]
    linear_combination (1)*hSquare
  have hNoAux : (-XX^4 + 7*XX^4*S - 21*XX^4*S^2 + 35*XX^4*S^3 - 35*XX^4*S^4 + 21*XX^4*S^5 - 7*XX^4*S^6 + XX^4*S^7 - 16*XX^6 + 48*XX^6*S - 48*XX^6*S^2 + 16*XX^6*S^3 + 128*XX^7*G) = 0 := by
    linear_combination (128*XX^7)*hInput - (-XX^4 + 6*XX^4*S - 15*XX^4*S^2 + 20*XX^4*S^3 - 15*XX^4*S^4 + 6*XX^4*S^5 - XX^4*S^6 - 2*XX^5*c + 10*XX^5*S*c - 20*XX^5*S^2*c + 20*XX^5*S^3*c - 10*XX^5*S^4*c + 2*XX^5*S^5*c - 16*XX^6 - 4*XX^6*c^2 + 32*XX^6*S + 16*XX^6*S*c^2 - 16*XX^6*S^2 - 24*XX^6*S^2*c^2 + 16*XX^6*S^3*c^2 - 4*XX^6*S^4*c^2 - 32*XX^7*c - 8*XX^7*c^3 + 32*XX^7*S*c + 24*XX^7*S*c^3 - 24*XX^7*S^2*c^3 + 8*XX^7*S^3*c^3 - 64*XX^8*c^2 - 16*XX^8*c^4 + 32*XX^8*S*c^4 - 16*XX^8*S^2*c^4 - 32*XX^9*c^5 + 32*XX^9*S*c^5 - 64*XX^10*c^6)*hAux
  have hNoRoot : (-XX^4 + 7*XX^4*Y - 21*XX^4*Y^2 + 35*XX^4*Y^3 - 35*XX^4*Y^4 + 21*XX^4*Y^5 - 7*XX^4*Y^6 + XX^4*Y^7 - 16*XX^6 + 48*XX^6*Y - 48*XX^6*Y^2 + 16*XX^6*Y^3 + 128*XX^7*G) = 0 := by
    linear_combination (1)*hNoAux - (7*XX^4 - 21*XX^4*Y + 35*XX^4*Y^2 - 35*XX^4*Y^3 + 21*XX^4*Y^4 - 7*XX^4*Y^5 + XX^4*Y^6 - 21*XX^4*S + 35*XX^4*S*Y - 35*XX^4*S*Y^2 + 21*XX^4*S*Y^3 - 7*XX^4*S*Y^4 + XX^4*S*Y^5 + 35*XX^4*S^2 - 35*XX^4*S^2*Y + 21*XX^4*S^2*Y^2 - 7*XX^4*S^2*Y^3 + XX^4*S^2*Y^4 - 35*XX^4*S^3 + 21*XX^4*S^3*Y - 7*XX^4*S^3*Y^2 + XX^4*S^3*Y^3 + 21*XX^4*S^4 - 7*XX^4*S^4*Y + XX^4*S^4*Y^2 - 7*XX^4*S^5 + XX^4*S^5*Y + XX^4*S^6 + 48*XX^6 - 48*XX^6*Y + 16*XX^6*Y^2 - 48*XX^6*S + 16*XX^6*S*Y + 16*XX^6*S^2)*hYLink
  have hReduced : (-64*XX^4 + 64*XX^4*Y + 448*XX^5 - 320*XX^5*Y - 960*XX^6 + 448*XX^6*Y + 640*XX^7 + 128*XX^7*G - 128*XX^7*Y) = 0 := by
    linear_combination hNoRoot - (-63*XX^4 + 57*XX^4*Y - 42*XX^4*Y^2 + 22*XX^4*Y^3 - 7*XX^4*Y^4 + XX^4*Y^5 + 196*XX^5 - 92*XX^5*Y + 28*XX^5*Y^2 - 4*XX^5*Y^3 - 160*XX^6 + 32*XX^6*Y)*hY
  have hNonzero1 : ((8192*XX^11) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 11) heq
    rw [show ((8192*XX^11) : PowerSeries ℚ) = term (8192) 11 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder0 : (2*XX^3)*G = (1 - 7*XX + 15*XX^2 - 10*XX^3)+(-1 + 5*XX - 7*XX^2 + 2*XX^3)*Y := by
    apply mul_left_cancel₀ hNonzero1
    linear_combination (128*XX^7)*hReduced - (0 : PowerSeries ℚ)*hY
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
  have hEuler3 : euler (2*XX^3) = (6*XX^3) := by
    conv_lhs => rw [show (2*XX^3) = term (2) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler4 : euler (1 - 7*XX + 15*XX^2 - 10*XX^3) = (-7*XX + 30*XX^2 - 30*XX^3) := by
    conv_lhs => rw [show (1 - 7*XX + 15*XX^2 - 10*XX^3) = term (1) 0 + term (-7) 1 + term (15) 2 + term (-10) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler5 : euler (-1 + 5*XX - 7*XX^2 + 2*XX^3) = (5*XX - 14*XX^2 + 6*XX^3) := by
    conv_lhs => rw [show (-1 + 5*XX - 7*XX^2 + 2*XX^3) = term (-1) 0 + term (5) 1 + term (-7) 2 + term (2) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hGradient0 := congrArg euler hOrder0
  rw [eulerMul (2*XX^3) (G), eulerAdd (1 - 7*XX + 15*XX^2 - 10*XX^3) ((-1 + 5*XX - 7*XX^2 + 2*XX^3)*Y),
    eulerMul (-1 + 5*XX - 7*XX^2 + 2*XX^3) Y] at hGradient0
  simp only [hEuler3, hEuler4, hEuler5] at hGradient0
  have hNonzero6 : ((4*XX^3) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 3) heq
    rw [show ((4*XX^3) : PowerSeries ℚ) = term (4) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder1 : (2*XX^3 - 8*XX^4)*(euler (G)) = (-3 + 26*XX - 71*XX^2 + 60*XX^3)+(3 - 20*XX + 37*XX^2 - 14*XX^3 - 4*XX^4)*Y := by
    apply mul_left_cancel₀ hNonzero6
    linear_combination (4*XX^3 - 16*XX^4)*hGradient0 - (12*XX^3 - 48*XX^4)*hOrder0 + (-2*XX^3 + 10*XX^4 - 14*XX^5 + 4*XX^6)*hYDeriv
  have hEuler7 : euler (2*XX^3 - 8*XX^4) = (6*XX^3 - 32*XX^4) := by
    conv_lhs => rw [show (2*XX^3 - 8*XX^4) = term (2) 3 + term (-8) 4 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler8 : euler (-3 + 26*XX - 71*XX^2 + 60*XX^3) = (26*XX - 142*XX^2 + 180*XX^3) := by
    conv_lhs => rw [show (-3 + 26*XX - 71*XX^2 + 60*XX^3) = term (-3) 0 + term (26) 1 + term (-71) 2 + term (60) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler9 : euler (3 - 20*XX + 37*XX^2 - 14*XX^3 - 4*XX^4) = (-20*XX + 74*XX^2 - 42*XX^3 - 16*XX^4) := by
    conv_lhs => rw [show (3 - 20*XX + 37*XX^2 - 14*XX^3 - 4*XX^4) = term (3) 0 + term (-20) 1 + term (37) 2 + term (-14) 3 + term (-4) 4 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hGradient1 := congrArg euler hOrder1
  rw [eulerMul (2*XX^3 - 8*XX^4) (euler (G)), eulerAdd (-3 + 26*XX - 71*XX^2 + 60*XX^3) ((3 - 20*XX + 37*XX^2 - 14*XX^3 - 4*XX^4)*Y),
    eulerMul (3 - 20*XX + 37*XX^2 - 14*XX^3 - 4*XX^4) Y] at hGradient1
  simp only [hEuler7, hEuler8, hEuler9] at hGradient1
  have hNonzero10 : ((-4*XX^3 + 16*XX^4) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 3) heq
    rw [show ((-4*XX^3 + 16*XX^4) : PowerSeries ℚ) = term (-4) 3 + term (16) 4 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder2 : (-2*XX^3 + 16*XX^4 - 32*XX^5)*(euler (euler (G))) = (-9 + 100*XX - 383*XX^2 + 568*XX^3 - 240*XX^4)+(9 - 82*XX + 237*XX^2 - 222*XX^3 + 32*XX^4 - 8*XX^5)*Y := by
    apply mul_left_cancel₀ hNonzero10
    linear_combination (4*XX^3 - 32*XX^4 + 64*XX^5)*hGradient1 - (12*XX^3 - 112*XX^4 + 256*XX^5)*hOrder1 + (6*XX^3 - 64*XX^4 + 234*XX^5 - 324*XX^6 + 104*XX^7 + 32*XX^8)*hYDeriv
  have hNonzero11 : ((2*XX^3 - 16*XX^4 + 32*XX^5) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 3) heq
    rw [show ((2*XX^3 - 16*XX^4 + 32*XX^5) : PowerSeries ℚ) = term (2) 3 + term (-16) 4 + term (32) 5 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hFinal : term (114) 0 * (G) + term (-306) 1 * (G) + term (-16) 2 * (G) + term (5) 0 * (euler (G)) + term (-32) 1 * (euler (G)) + term (84) 2 * (euler (G)) + term (-11) 0 * (euler (euler (G))) + term (70) 1 * (euler (euler (G))) + term (-104) 2 * (euler (euler (G))) = term (80) 2 := by
    apply mul_left_cancel₀ hNonzero11
    simp only [term, map_ofNat, map_neg, map_one, map_zero]
    linear_combination (114 - 1218*XX + 4256*XX^2 - 4768*XX^3 - 256*XX^4)*hOrder0 + (5 - 52*XX + 212*XX^2 - 336*XX^3)*hOrder1 + (11 - 70*XX + 104*XX^2)*hOrder2
  have hnCoeff := congrArg (coeff n) hFinal
  have hLag0 : 0 ≤ n := by omega
  have hLag1 : 1 ≤ n := by omega
  have hLag2 : 2 ≤ n := by omega
  have hRhs2 : n ≠ 2 := by omega
  simp only [map_add, map_zero, coeffTermMul, coeffTerm, coeffEuler, if_true, if_false, Nat.sub_zero, hLag0, hLag1, hLag2, hRhs2, Nat.cast_sub hLag1, Nat.cast_sub hLag2, Nat.cast_ofNat] at hnCoeff
  linear_combination ((1 : ℚ))*hnCoeff

end SqrtRecurrence_oeis_a026026

theorem OMA.solution : type_of% @OMA.S_oeis_a026026.main :=
  SqrtRecurrence_oeis_a026026.checked
