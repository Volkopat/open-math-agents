import OMAStatements.S_oeis_a176964

/-! The quadratic convolution determines an algebraic power series.
Differentiating a polynomial square identity gives a first-order linear
differential equation and hence the asserted coefficient recurrence. -/

namespace A176964Proof

open OMA.S_oeis_a176964 PowerSeries Finset
open scoped PowerSeries

private theorem prefixLength : ∀ n : ℕ, (aList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by rw [aList, List.length_append, prefixLength (n + 1)]; rfl

private theorem prefixStep (n i : ℕ) (hi : i ≤ n) :
    (aList (n+1)).getD i 0 = (aList n).getD i 0 := by
  cases n with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ n =>
    rw [show n.succ + 1 = n + 2 by omega, aList, List.getD_append]
    rw [prefixLength]
    omega

private theorem prefixCoefficient (n i : ℕ) (hi : i ≤ n) :
    (aList n).getD i 0 = a i := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    by_cases hs : i ≤ n
    · rw [prefixStep n i hs, ih hs]
    · have : i = n+1 := by omega
      subst i
      rfl

private theorem convRec (n : ℕ) : a (n + 2) =
    (∑ p ∈ range (n+2), a p * a (n+1-p)) - ((n : ℤ) + 2) + 1 := by
  unfold a
  rw [aList, List.getD_append_right]
  · rw [prefixLength, show n + 2 - (n + 1 + 1) = 0 by omega]
    change (∑ p ∈ range (n+2), (aList (n+1)).getD p 0 *
      (aList (n+1)).getD (n+1-p) 0) - ((n : ℤ) + 2) + 1 = _
    congr 1
    congr 1
    apply sum_congr rfl
    intro p hp
    have hpn := mem_range.mp hp
    rw [prefixCoefficient _ _ (by omega), prefixCoefficient _ _ (by omega)]
    rfl
  · rw [prefixLength]

private noncomputable abbrev Xz : PowerSeries ℤ := X
private noncomputable def A : PowerSeries ℤ := PowerSeries.mk a
private noncomputable def T : PowerSeries ℤ := PowerSeries.mk fun n => (n : ℤ) + 1

private theorem A_quad : A = 1 + PowerSeries.C 2 * Xz + Xz * A^2 - Xz^2 * T := by
  ext n
  rcases n with _ | _ | n
  · simp [A, Xz, a, aList]
  · have ht : coeff 1 (Xz^2*T) = 0 := by rw [coeff_X_pow_mul']; simp
    have hs : coeff 0 (A^2) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply]
      simp [A, a, aList]
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_one, hs, ht]
    norm_num [A, a, aList]
  · simp only [map_add, map_sub, coeff_C_mul, coeff_X, coeff_one, coeff_succ_X_mul,
      coeff_X_pow_mul', A, coeff_mk, Xz]
    have h0 : n.succ.succ ≠ 0 := by omega
    have h1 : n.succ.succ ≠ 1 := by omega
    have h2 : 2 ≤ n.succ.succ := by omega
    have hn : n.succ.succ - 2 = n := by omega
    simp only [h0, h1, h2, hn, if_false, if_true, mul_zero, add_zero, zero_add, T, coeff_mk]
    rw [pow_two, coeff_mul]
    simp only [coeff_mk]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * a j) (n+1)]
    linear_combination convRec n

private theorem T_clear : (1-Xz)^2 * T = 1 := by
  rw [show (1-Xz)^2*T = T - PowerSeries.C 2*(Xz*T) + Xz^2*T by
    simp only [map_ofNat]; ring]
  ext n
  rcases n with _ | _ | n
  · simp only [map_sub, map_add, coeff_C_mul, coeff_zero_X_mul, coeff_X_pow_mul', T,
      coeff_mk, coeff_one]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul', T,
      coeff_mk, coeff_one]
    norm_num
  · have h2 : 2 ≤ n.succ.succ := by omega
    have hz : n.succ.succ ≠ 0 := by omega
    simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul', T,
      coeff_mk, coeff_one, h2, hz, if_true, if_false]
    simp only [show n.succ.succ - 2 = n by omega, Nat.cast_succ]
    ring

private noncomputable def B : PowerSeries ℤ :=
  (1-Xz) - PowerSeries.C 2 * Xz * (1-Xz) * A

private noncomputable def G : PowerSeries ℤ :=
  1 - PowerSeries.C 6*Xz + Xz^2 + PowerSeries.C 16*Xz^3 - PowerSeries.C 8*Xz^4

private theorem squareRelation : B^2 = G := by
  have hquad : A - 1 - PowerSeries.C 2*Xz - Xz*A^2 = -(Xz^2*T) := by
    linear_combination A_quad
  have hclear : (1-Xz)^2 * (A - 1 - PowerSeries.C 2*Xz - Xz*A^2) = -Xz^2 := by
    rw [hquad]
    calc
      _ = -(Xz^2 * ((1-Xz)^2*T)) := by ring
      _ = _ := by rw [T_clear, mul_one]
  simp only [B, G, map_ofNat] at hclear ⊢
  linear_combination -4*Xz*hclear

private theorem derivativeMul (f g : PowerSeries ℤ) :
    d⁄dX ℤ (f*g) = f*d⁄dX ℤ g + g*d⁄dX ℤ f := by
  simpa only [smul_eq_mul] using (PowerSeries.derivative ℤ).leibniz f g

private theorem derivativeB : d⁄dX ℤ B =
    -1 - 2*(1-2*Xz)*A - 2*Xz*(1-Xz)*d⁄dX ℤ A := by
  simp only [B, map_sub, Derivation.map_one_eq_zero, derivative_X, derivativeMul,
    derivative_C]
  simp only [map_ofNat]
  ring

private theorem derivativeG : d⁄dX ℤ G = -6 + 2*Xz + 48*Xz^2 - 32*Xz^3 := by
  simp only [G, map_sub, map_add, Derivation.map_one_eq_zero, derivative_X, derivativeMul,
    derivative_C, derivative_pow]
  norm_num
  ring

private noncomputable def term (c : ℤ) (j : ℕ) : PowerSeries ℤ := PowerSeries.C c*Xz^j

private noncomputable def P : PowerSeries ℤ :=
  term 1 1 + term (-7) 2 + term 7 3 + term 15 4 + term (-24) 5 + term 8 6

private noncomputable def Q : PowerSeries ℤ :=
  term 1 0 + term (-5) 1 + term 9 2 + term (-9) 3

private noncomputable def R : PowerSeries ℤ :=
  term 1 0 + term 1 1 + term (-12) 2 + term 12 3 + term (-4) 4

private theorem differential : P*d⁄dX ℤ A + Q*A = R := by
  have hder := congrArg (PowerSeries.derivative ℤ) squareRelation
  rw [PowerSeries.derivative_pow] at hder
  have h : 2*G*d⁄dX ℤ B = (d⁄dX ℤ G)*B := by
    calc
      _ = ((2 : ℕ) * B^(2-1) * d⁄dX ℤ B)*B := by rw [← squareRelation]; norm_num; ring
      _ = _ := by rw [hder]
  rw [derivativeB, derivativeG] at h
  have hfour : (4 : PowerSeries ℤ) ≠ 0 := by
    intro heq
    have hc := congrArg (constantCoeff (R := ℤ)) heq
    simp only [map_ofNat, map_zero] at hc
    omega
  apply mul_left_cancel₀ hfour
  simp only [P, Q, R, term, B, G, map_one, map_neg, map_ofNat] at h ⊢
  linear_combination -h

private theorem coeffTermMul (c : ℤ) (k n : ℕ) (F : PowerSeries ℤ) :
    coeff n (term c k * F) = c * (if k ≤ n then coeff (n-k) F else 0) := by
  rw [term, mul_assoc, coeff_C_mul, coeff_X_pow_mul']

private theorem coeffTerm (c : ℤ) (k n : ℕ) :
    coeff n (term c k) = if n = k then c else 0 :=
  coeff_C_mul_X_pow c k n

theorem coefficientRec (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℤ)+1)*a n + (-7*(n : ℤ)+2)*a (n-1) + (7*(n : ℤ)-5)*a (n-2)
      + 3*(5*(n : ℤ)-18)*a (n-3) + 24*(-(n : ℤ)+4)*a (n-4)
      + 8*((n : ℤ)-5)*a (n-5) = 0 := by
  by_cases h5eq : n = 5
  · subst n
    decide +kernel
  have h := congrArg (coeff n) differential
  simp only [P, Q, R, add_mul, map_add, coeffTermMul, coeffTerm,
    coeff_derivative, A, coeff_mk] at h
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h6 : 6 ≤ n := by omega
  have hne (k : ℕ) (hk : k ≤ 4) : n ≠ k := by omega
  have index (j : ℕ) (hj : j+1 ≤ n) : n-(j+1)+1 = n-j := by omega
  simp only [Nat.zero_le, h1, h2, h3, h4, hn, h6, if_true, hne 0 (by decide),
    hne 1 (by decide), hne 2 (by decide), hne 3 (by decide), hne 4 (by decide), if_false,
    index 0 h1, index 1 h2, index 2 h3, index 3 h4, index 4 hn, index 5 h6,
    Nat.sub_zero, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3,
    Nat.cast_sub h4, Nat.cast_sub hn, Nat.cast_sub h6, Nat.cast_ofNat] at h
  linear_combination h

end A176964Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a176964.main :=
  A176964Proof.coefficientRec
