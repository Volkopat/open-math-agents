import OMAStatements.S_oeis_a081207

-- Problem: OEIS A081207. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a second order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives c1 A' + c0 A = c with c1 = 2RDQ, c0 = 2RQD' - (2RQ' + QR')D,
-- c = 2RQP' - (2RQ' + QR')P. Differentiating once more expresses A'' through A' and A, and the
-- operator of the recurrence, b2 (x d/dx)^2 + b1 (x d/dx) + b0, then sends A to a polynomial T.
-- Comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a081207 PowerSeries

lemma OMA.d_ofNat (n : ℕ) [n.AtLeastTwo] : d⁄dX ℚ (ofNat(n) : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ _

lemma OMA.hasSubst : HasSubst (R - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  unfold R
  simp

lemma OMA.S_sq : S * S = R := by
  unfold S
  have h := OMA.hasSubst
  have e : (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) := by norm_num
  rw [← subst_mul h, ← binomialSeries_add, e, binomialSeries_nat, pow_one, subst_add h, subst_X h,
    ← coe_substAlgHom h, map_one]
  ring

lemma OMA.coeff_theta (f : ℚ⟦X⟧) (m : ℕ) : coeff m (X * d⁄dX ℚ f) = (m : ℚ) * coeff m f := by
  rcases m with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma OMA.cXt (c : ℚ) (j N m : ℕ) (f : ℚ⟦X⟧) (h : N = m + j) :
    coeff N (C c * (X ^ j * (X * d⁄dX ℚ f))) = c * ((m : ℚ) * coeff m f) := by
  subst h
  rw [coeff_C_mul, coeff_X_pow_mul, OMA.coeff_theta]

lemma OMA.cXf (c : ℚ) (j N m : ℕ) (f : ℚ⟦X⟧) (h : N = m + j) :
    coeff N (C c * (X ^ j * f)) = c * coeff m f := by
  subst h
  rw [coeff_C_mul, coeff_X_pow_mul]

lemma OMA.cX0 (c : ℚ) (j N : ℕ) (h : j < N) : coeff N (C c * X ^ j : ℚ⟦X⟧) = 0 := by
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

lemma OMA.ne_of_cc (f : ℚ⟦X⟧) (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h


lemma OMA.cXtt (c : ℚ) (j N m : ℕ) (f : ℚ⟦X⟧) (h : N = m + j) :
    coeff N (C c * (X ^ j * (X * d⁄dX ℚ (X * d⁄dX ℚ f))))
      = c * ((m : ℚ) * ((m : ℚ) * coeff m f)) := by
  subst h
  rw [coeff_C_mul, coeff_X_pow_mul, OMA.coeff_theta, OMA.coeff_theta]

/-- The generating function of the sequence. -/
noncomputable def OMA.A : ℚ⟦X⟧ :=
    (((1 + X) * S)
      * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff m OMA.A := rfl

lemma OMA.dS : 2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * d⁄dX ℚ S = (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ) = ((1 + X) * S) := by
  unfold OMA.A
  have hD : constantCoeff (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧)
    = (0 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S + (1 + 1 * X : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.fo : (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + (-4 + 8 * X - 2 * X ^ 2 + 22 * X ^ 3 + 6 * X ^ 5 - 12 * X ^ 6 - 2 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * OMA.A = (0 : ℚ⟦X⟧) := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  linear_combination (2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (1 + 1 * X : ℚ⟦X⟧)) * F4
    - (2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (1 : ℚ⟦X⟧) + (1 + 1 * X : ℚ⟦X⟧) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧)) * F3 + ((1 + 1 * X : ℚ⟦X⟧) * (1 + 1 * X : ℚ⟦X⟧)) * hS

lemma OMA.fo2 : (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧) * d⁄dX ℚ (d⁄dX ℚ OMA.A) + ((-6 - 8 * X + 12 * X ^ 2 + 88 * X ^ 3 + 110 * X ^ 4 + 24 * X ^ 5 - 28 * X ^ 6 - 48 * X ^ 7 + 18 * X ^ 8 : ℚ⟦X⟧) + (-4 + 8 * X - 2 * X ^ 2 + 22 * X ^ 3 + 6 * X ^ 5 - 12 * X ^ 6 - 2 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧)) * d⁄dX ℚ OMA.A
    + (8 - 4 * X + 66 * X ^ 2 + 30 * X ^ 4 - 72 * X ^ 5 - 14 * X ^ 6 + 16 * X ^ 7 : ℚ⟦X⟧) * OMA.A = (0 : ℚ⟦X⟧) := by
  have E := congrArg (d⁄dX ℚ) OMA.fo
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.th2 : X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A) = X * X * d⁄dX ℚ (d⁄dX ℚ OMA.A) + X * d⁄dX ℚ OMA.A := by
  rw [Derivation.leibniz]
  simp only [derivative_X, smul_eq_mul]
  ring

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (-2 + 1 * X - 1 * X ^ 2 - 5 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (2 * X - 2 * X ^ 2 - 1 * X ^ 3 + 3 * X ^ 4 : ℚ⟦X⟧) * OMA.A) - (0 : ℚ⟦X⟧) = 0 := by
  have h1' := OMA.fo
  have h2' := OMA.fo2
  have h3' := OMA.th2
  have key : ((2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧) * (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (-2 + 1 * X - 1 * X ^ 2 - 5 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (2 * X - 2 * X ^ 2 - 1 * X ^ 3 + 3 * X ^ 4 : ℚ⟦X⟧) * OMA.A) - (0 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧) * (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧)) * h3'
        + ((1 : ℚ⟦X⟧) * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * X ^ 2 * (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧)) * h2'
        + ((1 : ℚ⟦X⟧) * (-2 * X + 14 * X ^ 2 - 14 * X ^ 3 - 22 * X ^ 4 - 76 * X ^ 5 + 76 * X ^ 6 + 202 * X ^ 7 + 242 * X ^ 8 + 68 * X ^ 9 - 116 * X ^ 10 - 62 * X ^ 11 - 22 * X ^ 12 + 46 * X ^ 13 - 10 * X ^ 14 : ℚ⟦X⟧)) * h1'
  have hc1 : (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧) ≠ 0 := by
    have e : (2 - 6 * X - 4 * X ^ 2 + 4 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 - 6 * X ^ 8 + 2 * X ^ 9 : ℚ⟦X⟧) = 2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (X ^ 0 * (1 + 1 * X : ℚ⟦X⟧)) := by ring
    rw [e]
    have h1 : (2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h2 : (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h3 : (1 + 1 * X : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (pow_ne_zero _ X_ne_zero) h3)
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc1 hc1)

theorem OMA.solution : type_of% @OMA.S_oeis_a081207.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hexp : C (1 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-2 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-1 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-2 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (1 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-2 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (1 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (-1 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-5 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A))
      + C (4 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A))
      + C (2 : ℚ) * (X ^ 1 * OMA.A)
      + C (-2 : ℚ) * (X ^ 2 * OMA.A)
      + C (-1 : ℚ) * (X ^ 3 * OMA.A)
      + C (3 : ℚ) * (X ^ 4 * OMA.A)
      = (0 : ℚ⟦X⟧) := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 4)) hexp
  have s0 : coeff (k + 4) (C (1 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (1 : ℚ) * (((k + 4 : ℕ) : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A)) :=
    OMA.cXtt _ 0 _ (k + 4) _ (by omega)
  have s1 : coeff (k + 4) (C (-2 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-2 : ℚ) * (((k + 3 : ℕ) : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A)) :=
    OMA.cXtt _ 1 _ (k + 3) _ (by omega)
  have s2 : coeff (k + 4) (C (-1 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-1 : ℚ) * (((k + 2 : ℕ) : ℚ) * (((k + 2 : ℕ) : ℚ) * coeff (k + 2) OMA.A)) :=
    OMA.cXtt _ 2 _ (k + 2) _ (by omega)
  have s3 : coeff (k + 4) (C (-2 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-2 : ℚ) * (((k + 1 : ℕ) : ℚ) * (((k + 1 : ℕ) : ℚ) * coeff (k + 1) OMA.A)) :=
    OMA.cXtt _ 3 _ (k + 1) _ (by omega)
  have s4 : coeff (k + 4) (C (1 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (1 : ℚ) * (((k + 0 : ℕ) : ℚ) * (((k + 0 : ℕ) : ℚ) * coeff (k + 0) OMA.A)) :=
    OMA.cXtt _ 4 _ (k + 0) _ (by omega)
  have t0 : coeff (k + 4) (C (-2 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (-2 : ℚ) * (((k + 4 : ℕ) : ℚ) * coeff (k + 4) OMA.A) :=
    OMA.cXt _ 0 _ (k + 4) _ (by omega)
  have t1 : coeff (k + 4) (C (1 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (1 : ℚ) * (((k + 3 : ℕ) : ℚ) * coeff (k + 3) OMA.A) :=
    OMA.cXt _ 1 _ (k + 3) _ (by omega)
  have t2 : coeff (k + 4) (C (-1 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (-1 : ℚ) * (((k + 2 : ℕ) : ℚ) * coeff (k + 2) OMA.A) :=
    OMA.cXt _ 2 _ (k + 2) _ (by omega)
  have t3 : coeff (k + 4) (C (-5 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A)))
      = (-5 : ℚ) * (((k + 1 : ℕ) : ℚ) * coeff (k + 1) OMA.A) :=
    OMA.cXt _ 3 _ (k + 1) _ (by omega)
  have t4 : coeff (k + 4) (C (4 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A)))
      = (4 : ℚ) * (((k + 0 : ℕ) : ℚ) * coeff (k + 0) OMA.A) :=
    OMA.cXt _ 4 _ (k + 0) _ (by omega)
  have f1 : coeff (k + 4) (C (2 : ℚ) * (X ^ 1 * OMA.A))
      = (2 : ℚ) * coeff (k + 3) OMA.A := OMA.cXf _ 1 _ (k + 3) _ (by omega)
  have f2 : coeff (k + 4) (C (-2 : ℚ) * (X ^ 2 * OMA.A))
      = (-2 : ℚ) * coeff (k + 2) OMA.A := OMA.cXf _ 2 _ (k + 2) _ (by omega)
  have f3 : coeff (k + 4) (C (-1 : ℚ) * (X ^ 3 * OMA.A))
      = (-1 : ℚ) * coeff (k + 1) OMA.A := OMA.cXf _ 3 _ (k + 1) _ (by omega)
  have f4 : coeff (k + 4) (C (3 : ℚ) * (X ^ 4 * OMA.A))
      = (3 : ℚ) * coeff (k + 0) OMA.A := OMA.cXf _ 4 _ (k + 0) _ (by omega)
  simp only [map_add, map_zero, s0, s1, s2, s3, s4, t0, t1, t2, t3, t4, f1, f2, f3, f4] at hc
  have e0 : a (k + 4) = coeff (k + 4) OMA.A := by
    have h : k + 4 = k + 4 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 4 - 1) = coeff (k + 3) OMA.A := by
    have h : k + 4 - 1 = k + 3 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 4 - 2) = coeff (k + 2) OMA.A := by
    have h : k + 4 - 2 = k + 2 := by omega
    rw [OMA.a_eq, h]
  have e3 : a (k + 4 - 3) = coeff (k + 1) OMA.A := by
    have h : k + 4 - 3 = k + 1 := by omega
    rw [OMA.a_eq, h]
  have e4 : a (k + 4 - 4) = coeff (k + 0) OMA.A := by
    have h : k + 4 - 4 = k + 0 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2, e3, e4]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
