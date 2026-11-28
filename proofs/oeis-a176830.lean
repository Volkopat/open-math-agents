import OMAStatements.S_oeis_a176830

/-! The quadratic convolution determines an algebraic power series.
Differentiating a polynomial square identity gives a first-order linear
differential equation and hence the asserted coefficient recurrence. -/

-- Original Lean proof: @romechenko.

namespace A176830Proof

open OMA.S_oeis_a176830 PowerSeries Finset
private noncomputable abbrev D := PowerSeries.derivative (R := ℤ)

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
    (∑ p ∈ range (n+2), a p * a (n+1-p)) + ((n : ℤ) + 1) := by
  unfold a
  rw [aList, List.getD_append_right]
  · rw [prefixLength, show n + 2 - (n + 1 + 1) = 0 by omega]
    change (∑ p ∈ range (n+2), (aList (n+1)).getD p 0 *
      (aList (n+1)).getD (n+1-p) 0) + ((n : ℤ) + 1) = _
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

private theorem A_quad : A = 1 + PowerSeries.C 3 * Xz + Xz * A^2 + Xz^2 * T := by
  ext n
  rcases n with _ | _ | n
  · simp [A, Xz, a, aList]
  · have ht : coeff 1 (Xz^2*T) = 0 := by rw [coeff_X_pow_mul']; simp
    have hs : coeff 0 (A^2) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply]
      simp [A, a, aList]
    simp only [map_add, coeff_C_mul, coeff_succ_X_mul, coeff_one, hs, ht]
    norm_num [A, a, aList]
  · simp only [map_add, coeff_C_mul, coeff_X, coeff_one, coeff_succ_X_mul,
      coeff_X_pow_mul', A, coeff_mk, Xz]
    have h0 : n.succ.succ ≠ 0 := by omega
    have h1 : n.succ.succ ≠ 1 := by omega
    have h2 : 2 ≤ n.succ.succ := by omega
    have hn : n.succ.succ - 2 = n := by omega
    simp only [h0, h1, h2, hn, if_false, if_true, mul_zero, add_zero, zero_add, T, coeff_mk]
    rw [pow_two, coeff_mul]
    simp only [coeff_mk]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * a j) (n+1)]
    exact convRec n

private theorem T_clear : (1-Xz)^2 * T = 1 := by
  have firstDiff : (1-Xz) * T = PowerSeries.mk 1 := by
    ext n
    cases n <;> simp [sub_mul, T, Xz, Nat.cast_succ]
  have secondDiff : (1-Xz) * PowerSeries.mk 1 = 1 := by
    ext n
    cases n <;> simp [sub_mul, Xz]
  rw [pow_two, mul_assoc, firstDiff, secondDiff]

private noncomputable def B : PowerSeries ℤ :=
  (1-Xz) - PowerSeries.C 2 * Xz * (1-Xz) * A

private noncomputable def G : PowerSeries ℤ :=
  1 - PowerSeries.C 6*Xz - PowerSeries.C 3 * Xz^2 +
    PowerSeries.C 16*Xz^3 - PowerSeries.C 12*Xz^4

private theorem squareRelation : B^2 = G := by
  have hquad : A - 1 - PowerSeries.C 3*Xz - Xz*A^2 = Xz^2*T := by
    linear_combination A_quad
  have hclear : (1-Xz)^2 * (A - 1 - PowerSeries.C 3*Xz - Xz*A^2) = Xz^2 := by
    rw [hquad]
    calc
      _ = Xz^2 * ((1-Xz)^2*T) := by ring
      _ = _ := by rw [T_clear, mul_one]
  simp only [B, G, map_ofNat] at hclear ⊢
  linear_combination -4*Xz*hclear

private theorem derivativeMul (f g : PowerSeries ℤ) :
    D (f*g) = f*D g + g*D f := by
  simpa only [smul_eq_mul] using (D).leibniz f g

private theorem derivativeB : D B =
    -1 - 2*(1-2*Xz)*A - 2*Xz*(1-Xz)*D A := by
  simp only [B, map_sub, Derivation.map_one_eq_zero, derivative_X, derivativeMul,
    derivative_C]
  simp only [map_ofNat]
  ring

private theorem derivativeG : D G = -6 - 6*Xz + 48*Xz^2 - 48*Xz^3 := by
  simp only [G, map_sub, map_add, Derivation.map_one_eq_zero, derivative_X, derivativeMul,
    derivative_C, derivative_pow]
  norm_num
  ring

private noncomputable def term (c : ℤ) (j : ℕ) : PowerSeries ℤ := PowerSeries.C c*Xz^j

private noncomputable def P : PowerSeries ℤ :=
  term 1 1 + term (-7) 2 + term 3 3 + term 19 4 + term (-28) 5 + term 12 6

private noncomputable def Q : PowerSeries ℤ :=
  term 1 0 + term (-5) 1 + term 9 2 + term (-5) 3 + term 4 4

private noncomputable def R : PowerSeries ℤ :=
  term 1 0 + term 3 1 + term (-12) 2 + term 16 3 + term (-6) 4

private theorem differential : P*D A + Q*A = R := by
  have hder := congrArg (D) squareRelation
  rw [PowerSeries.derivative_pow] at hder
  have h : 2*G*D B = (D G)*B := by
    calc
      _ = ((2 : ℕ) * B^(2-1) * D B)*B := by rw [← squareRelation]; norm_num; ring
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

private theorem coeffDerivativeTerm (c : ℤ) (k n : ℕ) (h : k ≤ n + 1) :
    coeff n (term c k * D A) = c * ((n : ℤ) + 1 - k) * a (n + 1 - k) := by
  rw [coeffTermMul]
  by_cases hk : k ≤ n
  · simp [hk, coeff_derivative, A, Nat.cast_sub hk, show n - k + 1 = n + 1 - k by omega]
    ring
  · have he : k = n + 1 := by omega
    subst k
    simp [if_neg hk]

theorem coefficientRec (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℤ)+1)*a n + (-7*(n : ℤ)+2)*a (n-1) + 3*((n : ℤ)+1)*a (n-2)
      + (19*(n : ℤ)-62)*a (n-3) + 4*(-7*(n : ℤ)+29)*a (n-4)
      + 12*((n : ℤ)-5)*a (n-5) = 0 := by
  have h := congrArg (coeff n) differential
  simp (disch := omega) only [P, Q, R, add_mul, map_add, coeffDerivativeTerm] at h
  have idx (k : ℕ) (hk : 0 < k) : n + 1 - k = n - (k - 1) := by omega
  simp (disch := omega) only [coeffTermMul, coeffTerm, A, coeff_mk, if_pos, if_neg, idx] at h
  norm_num at h
  linear_combination h

end A176830Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a176830.main :=
  A176830Proof.coefficientRec
