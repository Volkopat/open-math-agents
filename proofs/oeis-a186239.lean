import OMAStatements.S_oeis_a186239

/-! The root equation and the generating-function relation give polynomial
certificates for the Euler derivatives. Taking coefficients yields the recurrence. -/

open PowerSeries
open scoped PowerSeries

namespace SqrtRecurrence_oeis_a186239

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

private theorem derivativeNumeral (n : ℕ) [n.AtLeastTwo] :
    derivative ℚ (ofNat(n) : PowerSeries ℚ) = 0 :=
  (derivative ℚ).map_natCast n

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 10000 in
theorem checked : type_of% @OMA.S_oeis_a186239.main := by

  intro G hInput0 n hn
  have hF : (-1 + G - XX*G - XX^2*G^2 - 2*XX^3*G^3) = 0 := by
    linear_combination hInput0
  have hEuler1 : euler (-1 + G - XX*G - XX^2*G^2 - 2*XX^3*G^3) = (-XX*G - 2*XX^2*G^2 - 6*XX^3*G^3) + (1 - XX - 2*XX^2*G - 6*XX^3*G^2)*euler G := by
    simp only [euler, derivativeMul, derivative_pow, derivative_X, map_add, map_sub,
      map_neg, derivativeNumeral, Derivation.map_one_eq_zero, map_zero]
    norm_num <;> ring
  have hDifferential := congrArg euler hF
  rw [hEuler1, show euler 0 = 0 by simp [euler]] at hDifferential
  have hOrder0 : (1 : PowerSeries ℚ)*G = G := one_mul G
  have hNonzero2 : ((8*XX^9) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 9) heq
    rw [show ((8*XX^9) : PowerSeries ℚ) = term (8) 9 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder1 : (8 - 23*XX - 14*XX^2 - 83*XX^3)*(euler (G)) = (12 - 12*G - 10*XX + 30*XX*G + 5*XX^2*G - 2*XX^2*G^2 + 83*XX^3*G - 34*XX^3*G^2) := by
    apply mul_left_cancel₀ hNonzero2
    linear_combination (-8*XX^9)*((-8 + 15*XX - XX^2 + 14*XX^2*G + 24*XX^3*G + 24*XX^3*G^2 - 20*XX^4*G^2)*hDifferential + (-30*XX^2 - 82*XX^3 - 72*XX^3*G + 60*XX^4*G)*euler G*hF) + (96*XX^9 - 80*XX^10 + 240*XX^11*G + 656*XX^12*G + 576*XX^12*G^2 - 480*XX^13*G^2)*hF
  have hEuler3 : euler (8 - 23*XX - 14*XX^2 - 83*XX^3) = (-23*XX - 28*XX^2 - 249*XX^3) := by
    conv_lhs => rw [show (8 - 23*XX - 14*XX^2 - 83*XX^3) = term (8) 0 + term (-23) 1 + term (-14) 2 + term (-83) 3 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring]
    simp only [euler, term, map_add, map_zero, derivativeMul, derivative_C,
      derivative_X, derivative_pow]
    norm_num <;> simp only [map_ofNat, map_neg, map_one, map_zero] <;> ring
  have hEuler4 : euler (12 - 12*G - 10*XX + 30*XX*G + 5*XX^2*G - 2*XX^2*G^2 + 83*XX^3*G - 34*XX^3*G^2) = (-10*XX + 30*XX*G + 10*XX^2*G - 4*XX^2*G^2 + 249*XX^3*G - 102*XX^3*G^2) + (-12 + 30*XX + 5*XX^2 - 4*XX^2*G + 83*XX^3 - 68*XX^3*G)*euler G := by
    simp only [euler, derivativeMul, derivative_pow, derivative_X, map_add, map_sub,
      map_neg, derivativeNumeral, Derivation.map_one_eq_zero, map_zero]
    norm_num <;> ring
  have hGradient1 := congrArg euler hOrder1
  rw [eulerMul (8 - 23*XX - 14*XX^2 - 83*XX^3) (euler (G)), hEuler3, hEuler4] at hGradient1
  have hNonzero5 : ((-16*XX^3 + 46*XX^4 + 28*XX^5 + 166*XX^6) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 3) heq
    rw [show ((-16*XX^3 + 46*XX^4 + 28*XX^5 + 166*XX^6) : PowerSeries ℚ) = term (-16) 3 + term (46) 4 + term (28) 5 + term (166) 6 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder2 : (64 - 368*XX + 305*XX^2 - 684*XX^3 + 4014*XX^4 + 2324*XX^5 + 6889*XX^6)*(euler (euler (G))) = (-144 + 144*G + 672*XX - 752*XX*G - 40*XX^2 + 608*XX^2*G + 40*XX^2*G^2 + 2638*XX^3 - 2139*XX^3*G + 270*XX^3*G^2 - 2490*XX^4 + 5691*XX^4*G - 1662*XX^4*G^2 + 83*XX^5*G - 1854*XX^5*G^2 + 6889*XX^6*G - 8466*XX^6*G^2) := by
    apply mul_left_cancel₀ hNonzero5
    linear_combination (-2*XX^3)*((64 - 368*XX + 305*XX^2 - 684*XX^3 + 4014*XX^4 + 2324*XX^5 + 6889*XX^6)*hGradient1 - (-184*XX + 305*XX^2 - 1026*XX^3 + 8028*XX^4 + 5810*XX^5 + 20667*XX^6)*hOrder1 + (-96 + 516*XX - 482*XX^2 - 32*XX^2*G + 1125*XX^3 - 452*XX^3*G - 4469*XX^4 + 1620*XX^4*G - 1577*XX^5 + 1284*XX^5*G - 6889*XX^6 + 5644*XX^6*G)*hOrder1) + (64*XX^4 + 1992*XX^5 + 12128*XX^6 - 57648*XX^7 - 54944*XX^8 - 191896*XX^9)*hF
  have hNonzero6 : ((64 - 368*XX + 305*XX^2 - 684*XX^3 + 4014*XX^4 + 2324*XX^5 + 6889*XX^6) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 0) heq
    rw [show ((64 - 368*XX + 305*XX^2 - 684*XX^3 + 4014*XX^4 + 2324*XX^5 + 6889*XX^6) : PowerSeries ℚ) = term (64) 0 + term (-368) 1 + term (305) 2 + term (-684) 3 + term (4014) 4 + term (2324) 5 + term (6889) 6 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hFinal : term (12) 0 * (G) + term (-50) 1 * (G) + term (-366) 2 * (G) + term (-606) 3 * (G) + term (-2822) 4 * (G) + term (20) 0 * (euler (G)) + term (135) 1 * (euler (G)) + term (-831) 2 * (euler (G)) + term (-927) 3 * (euler (G)) + term (-4233) 4 * (euler (G)) + term (8) 0 * (euler (euler (G))) + term (113) 1 * (euler (euler (G))) + term (-405) 2 * (euler (euler (G))) + term (-321) 3 * (euler (euler (G))) + term (-1411) 4 * (euler (euler (G))) = term (12) 0 + term (-10) 1 := by
    apply mul_left_cancel₀ hNonzero6
    simp only [term, map_ofNat, map_neg, map_one, map_zero]
    linear_combination (768 - 7616*XX - 1364*XX^2 + 72446*XX^3 + 13138*XX^4 + 931198*XX^5 - 1948862*XX^6 - 1697270*XX^7 - 15257226*XX^8 - 10733062*XX^9 - 19440758*XX^10)*hOrder0 + (160 + 620*XX - 10033*XX^2 + 8147*XX^3 - 12114*XX^4 + 179310*XX^5 + 136203*XX^6 + 351339*XX^7)*hOrder1 + (8 + 113*XX - 405*XX^2 - 321*XX^3 - 1411*XX^4)*hOrder2
  have hCoefficients := congrArg (coeff n) hFinal
  have hlo0 : 0 ≤ n := by omega
  have hlo1 : 1 ≤ n := by omega
  have hlo2 : 2 ≤ n := by omega
  have hlo3 : 3 ≤ n := by omega
  have hlo4 : 4 ≤ n := by omega
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  simp only [map_add, map_zero, coeffTermMul, coeffTerm, coeffEuler, if_true, if_false, Nat.sub_zero, hlo0, hlo1, hlo2, hlo3, hlo4, hne0, hne1, Nat.cast_sub hlo1, Nat.cast_sub hlo2, Nat.cast_sub hlo3, Nat.cast_sub hlo4, Nat.cast_ofNat] at hCoefficients
  linear_combination ((1 : ℚ))*hCoefficients

end SqrtRecurrence_oeis_a186239

theorem OMA.solution : type_of% @OMA.S_oeis_a186239.main :=
  SqrtRecurrence_oeis_a186239.checked
