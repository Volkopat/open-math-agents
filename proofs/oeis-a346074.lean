import OMAStatements.S_oeis_a346074

/-! The root equation and the generating-function relation give polynomial
certificates for the Euler derivatives. Taking coefficients yields the recurrence. -/

open PowerSeries
open scoped PowerSeries

namespace SqrtRecurrence_oeis_a346074

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
theorem checked : ∀ G : ℚ⟦X⟧, (1-X)*G = 1+X^5*(1-X)*G^2 →
    ∀ n : ℕ, 6 ≤ n → ((n : ℚ)+5)*coeff n G + 2*(-(n : ℚ)-4)*coeff (n-1) G +
      ((n : ℚ)+3)*coeff (n-2) G + 2*(-2*(n : ℚ)+5)*coeff (n-5) G +
      4*((n : ℚ)-3)*coeff (n-6) G = 0 := by

  intro G hInput0 n hn
  have hF : (-1 + G - XX*G - XX^5*G^2 + XX^6*G^2) = 0 := by
    linear_combination hInput0
  have hEuler1 : euler (-1 + G - XX*G - XX^5*G^2 + XX^6*G^2) = (-XX*G - 5*XX^5*G^2 + 6*XX^6*G^2) + (1 - XX - 2*XX^5*G + 2*XX^6*G)*euler G := by
    simp only [euler, derivativeMul, derivative_pow, derivative_X, map_add, map_sub,
      map_neg, derivativeNumeral, Derivation.map_one_eq_zero, map_zero]
    norm_num <;> ring
  have hDifferential := congrArg euler hF
  rw [hEuler1, show euler 0 = 0 by simp [euler]] at hDifferential
  have hOrder0 : (1 : PowerSeries ℚ)*G = G := one_mul G
  have hNonzero2 : ((-XX^10 + XX^11) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 10) heq
    rw [show ((-XX^10 + XX^11) : PowerSeries ℚ) = term (-1) 10 + term (1) 11 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hOrder1 : (1 - 2*XX + XX^2 - 4*XX^5 + 4*XX^6)*(euler (G)) = (5 - 5*G - 4*XX + 10*XX*G - 5*XX^2*G + 10*XX^5*G - 12*XX^6*G) := by
    apply mul_left_cancel₀ hNonzero2
    linear_combination (XX^10 - 2*XX^11 + XX^12)*((-1 + 2*XX^5*G)*hDifferential + (-4*XX^5)*euler G*hF) + (-5*XX^10 + 9*XX^11 - 4*XX^12 - 10*XX^15*G + 22*XX^16*G - 12*XX^17*G)*hF
  have hNonzero3 : ((1 - 2*XX + XX^2 - 4*XX^5 + 4*XX^6) : PowerSeries ℚ) ≠ 0 := by
    intro heq
    have hh := congrArg (coeff 0) heq
    rw [show ((1 - 2*XX + XX^2 - 4*XX^5 + 4*XX^6) : PowerSeries ℚ) = term (1) 0 + term (-2) 1 + term (1) 2 + term (-4) 5 + term (4) 6 by
      simp only [term, map_ofNat, map_neg, map_one, map_zero]
      <;> ring] at hh
    simp only [map_add, map_zero, coeffTerm] at hh
    norm_num at hh
  have hFinal : term (5) 0 * (G) + term (-10) 1 * (G) + term (5) 2 * (G) + term (-10) 5 * (G) + term (12) 6 * (G) + term (1) 0 * (euler (G)) + term (-2) 1 * (euler (G)) + term (1) 2 * (euler (G)) + term (-4) 5 * (euler (G)) + term (4) 6 * (euler (G)) = term (5) 0 + term (-4) 1 := by
    apply mul_left_cancel₀ hNonzero3
    simp only [term, map_ofNat, map_neg, map_one, map_zero]
    linear_combination (5 - 20*XX + 30*XX^2 - 20*XX^3 + 5*XX^4 - 30*XX^5 + 92*XX^6 - 94*XX^7 + 32*XX^8 + 40*XX^10 - 88*XX^11 + 48*XX^12)*hOrder0 + (1 - 2*XX + XX^2 - 4*XX^5 + 4*XX^6)*hOrder1
  have hCoefficients := congrArg (coeff n) hFinal
  have hlo0 : 0 ≤ n := by omega
  have hlo1 : 1 ≤ n := by omega
  have hlo2 : 2 ≤ n := by omega
  have hlo5 : 5 ≤ n := by omega
  have hlo6 : 6 ≤ n := by omega
  have hne0 : n ≠ 0 := by omega
  have hne1 : n ≠ 1 := by omega
  simp only [map_add, map_zero, coeffTermMul, coeffTerm, coeffEuler, if_true, if_false, Nat.sub_zero, hlo0, hlo1, hlo2, hlo5, hlo6, hne0, hne1, Nat.cast_sub hlo1, Nat.cast_sub hlo2, Nat.cast_sub hlo5, Nat.cast_sub hlo6, Nat.cast_ofNat] at hCoefficients
  linear_combination ((1 : ℚ))*hCoefficients

end SqrtRecurrence_oeis_a346074

namespace GapFiveConvolutionGF



private noncomputable def G : ℚ⟦X⟧ := mk fun n => (OMA.S_oeis_a346074.a n : ℚ)

private noncomputable def U : ℚ⟦X⟧ := mk fun _ => 1

private theorem geomEquation : (1-X)*U = 1 := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero => simp [U]
  | succ n => simp [U, coeff_succ_X_mul]

private theorem convolutionEquation : G = U + X^5*G^2 := by
  apply PowerSeries.ext
  intro n
  rw [map_add, coeff_X_pow_mul']
  by_cases hn : n < 5
  · rw [if_neg (by omega : ¬ 5 ≤ n)]
    interval_cases n <;> norm_num [G,U,OMA.S_oeis_a346074.a]
  · obtain ⟨m,rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
    rw [if_pos (by omega : 5 ≤ m+5), Nat.add_sub_cancel, pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [G, U, coeff_mk, Nat.succ_eq_add_one]
    rw [OMA.S_oeis_a346074.a, ← Fin.sum_univ_eq_sum_range]
    push_cast
    rfl

private theorem checked : type_of% @OMA.S_oeis_a346074.main := by
  have hgf : (1-X)*G = 1+X^5*(1-X)*G^2 := by
    linear_combination (1-X)*convolutionEquation + geomEquation
  intro n hn
  have h := SqrtRecurrence_oeis_a346074.checked G hgf n hn
  simp only [G, coeff_mk] at h
  exact_mod_cast h

end GapFiveConvolutionGF

theorem OMA.solution : type_of% @OMA.S_oeis_a346074.main := GapFiveConvolutionGF.checked
