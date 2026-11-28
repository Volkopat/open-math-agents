import OMAStatements.S_oeis_a128096

-- Problem: OEIS A128096. The sequence is given by the generating function
-- A(x) = (P + Q * sqrt(R)) / D with polynomials P, Q, D, R; the conjectured recurrence is the
-- coefficientwise form of a second order linear differential equation for A.
-- Proof. S = sqrt(R) satisfies S^2 = R, hence 2 R S' = R' S. Differentiating A D = P + Q S and
-- eliminating S and S' gives c1 A' + c0 A = c with c1 = 2RDQ, c0 = 2RQD' - (2RQ' + QR')D,
-- c = 2RQP' - (2RQ' + QR')P. Differentiating once more expresses A'' through A' and A, and the
-- operator of the recurrence, b2 (x d/dx)^2 + b1 (x d/dx) + b0, then sends A to a polynomial T.
-- Comparing the coefficients of x^N for N large gives the recurrence.

open OMA.S_oeis_a128096 PowerSeries

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
    ((2 - 5 * X + 2 * X ^ 2 - 3 * X ^ 3 + 2 * X ^ 4 - X ^ 5 + (-2 + 3 * X - X ^ 2 + X ^ 3) * S)
      * (2 : PowerSeries ℚ)⁻¹)

lemma OMA.a_eq (m : ℕ) : a m = coeff (m + 4) OMA.A := rfl

lemma OMA.dS : 2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * d⁄dX ℚ S = (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * S := by
  have E := congrArg (d⁄dX ℚ) OMA.S_sq
  have hR : R = (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) := rfl
  have h2 := OMA.S_sq
  rw [hR] at E h2
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination S * E - (2 * d⁄dX ℚ S) * h2

lemma OMA.AD : OMA.A * (2 : PowerSeries ℚ) = (2 - 5 * X + 2 * X ^ 2 - 3 * X ^ 3 + 2 * X ^ 4 - X ^ 5 + (-2 + 3 * X - X ^ 2 + X ^ 3) * S) := by
  unfold OMA.A
  have hD : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
    norm_num
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD, mul_one]

lemma OMA.dAD : (2 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + OMA.A * (0 : ℚ⟦X⟧)
    = (-5 + 4 * X - 9 * X ^ 2 + 8 * X ^ 3 - 5 * X ^ 4 : ℚ⟦X⟧) + (3 - 2 * X + 3 * X ^ 2 : ℚ⟦X⟧) * S + (-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧) * d⁄dX ℚ S := by
  have E := congrArg (d⁄dX ℚ) OMA.AD
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.fo : (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ OMA.A + (-20 + 36 * X - 32 * X ^ 2 + 92 * X ^ 3 - 48 * X ^ 4 + 52 * X ^ 5 - 20 * X ^ 6 : ℚ⟦X⟧) * OMA.A = (-40 * X ^ 4 + 24 * X ^ 5 - 48 * X ^ 6 - 8 * X ^ 7 + 24 * X ^ 8 : ℚ⟦X⟧) := by
  have F3 := OMA.AD
  have F4 := OMA.dAD
  have hS := OMA.dS
  linear_combination (2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧)) * F4
    - (2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (3 - 2 * X + 3 * X ^ 2 : ℚ⟦X⟧) + (-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧)) * F3 + ((-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧) * (-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧)) * hS

lemma OMA.fo2 : (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧) * d⁄dX ℚ (d⁄dX ℚ OMA.A) + ((28 - 40 * X + 48 * X ^ 2 - 144 * X ^ 3 + 80 * X ^ 4 - 72 * X ^ 5 + 28 * X ^ 6 : ℚ⟦X⟧) + (-20 + 36 * X - 32 * X ^ 2 + 92 * X ^ 3 - 48 * X ^ 4 + 52 * X ^ 5 - 20 * X ^ 6 : ℚ⟦X⟧)) * d⁄dX ℚ OMA.A
    + (36 - 64 * X + 276 * X ^ 2 - 192 * X ^ 3 + 260 * X ^ 4 - 120 * X ^ 5 : ℚ⟦X⟧) * OMA.A = (-160 * X ^ 3 + 120 * X ^ 4 - 288 * X ^ 5 - 56 * X ^ 6 + 192 * X ^ 7 : ℚ⟦X⟧) := by
  have E := congrArg (d⁄dX ℚ) OMA.fo
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    OMA.d_ofNat, Derivation.map_one_eq_zero, map_zero, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at E
  linear_combination E

lemma OMA.th2 : X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A) = X * X * d⁄dX ℚ (d⁄dX ℚ OMA.A) + X * d⁄dX ℚ OMA.A := by
  rw [Derivation.leibniz]
  simp only [derivative_X, smul_eq_mul]
  ring

lemma OMA.ode : (1 : ℚ⟦X⟧) * ((-2176 + 6616 * X - 2352 * X ^ 2 + 2088 * X ^ 3 - 6704 * X ^ 4 + 2264 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (17186 - 52057 * X + 22448 * X ^ 2 - 10247 * X ^ 3 + 45764 * X ^ 4 - 15333 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (37525 * X - 45458 * X ^ 2 + 24681 * X ^ 3 - 71306 * X ^ 4 + 20065 * X ^ 5 : ℚ⟦X⟧) * OMA.A) - (31530 * X ^ 5 - 7800 * X ^ 6 + 3090 * X ^ 7 : ℚ⟦X⟧) = 0 := by
  have h1' := OMA.fo
  have h2' := OMA.fo2
  have h3' := OMA.th2
  have key : ((-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧) * (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧))
      * ((1 : ℚ⟦X⟧) * ((-2176 + 6616 * X - 2352 * X ^ 2 + 2088 * X ^ 3 - 6704 * X ^ 4 + 2264 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))
    + (17186 - 52057 * X + 22448 * X ^ 2 - 10247 * X ^ 3 + 45764 * X ^ 4 - 15333 * X ^ 5 : ℚ⟦X⟧) * (X * d⁄dX ℚ OMA.A)
    + (37525 * X - 45458 * X ^ 2 + 24681 * X ^ 3 - 71306 * X ^ 4 + 20065 * X ^ 5 : ℚ⟦X⟧) * OMA.A) - (31530 * X ^ 5 - 7800 * X ^ 6 + 3090 * X ^ 7 : ℚ⟦X⟧)) = 0 := by
    linear_combination
      ((1 : ℚ⟦X⟧) * (-2176 + 6616 * X - 2352 * X ^ 2 + 2088 * X ^ 3 - 6704 * X ^ 4 + 2264 * X ^ 5 : ℚ⟦X⟧) * (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧) * (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧)) * h3'
        + ((1 : ℚ⟦X⟧) * (-2176 + 6616 * X - 2352 * X ^ 2 + 2088 * X ^ 3 - 6704 * X ^ 4 + 2264 * X ^ 5 : ℚ⟦X⟧) * X ^ 2 * (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧)) * h2'
        + ((1 : ℚ⟦X⟧) * (-120080 * X + 801216 * X ^ 2 - 1794948 * X ^ 3 + 1857036 * X ^ 4 - 2455388 * X ^ 5 + 4072264 * X ^ 6 - 3364180 * X ^ 7 + 2556820 * X ^ 8 - 2720340 * X ^ 9 + 1666568 * X ^ 10 - 933692 * X ^ 11 + 411980 * X ^ 12 - 70388 * X ^ 13 : ℚ⟦X⟧)) * h1'
  have hc1 : (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-8 + 28 * X - 20 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 4 + 16 * X ^ 5 - 12 * X ^ 6 + 4 * X ^ 7 : ℚ⟦X⟧) = 2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) * (2 : ℚ⟦X⟧) * (X ^ 0 * (-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧)) := by ring
    rw [e]
    have h1 : (2 * (1 - 2 * X - 1 * X ^ 2 - 2 * X ^ 3 + 1 * X ^ 4 : ℚ⟦X⟧) : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h2 : (2 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    have h3 : (-2 + 3 * X - 1 * X ^ 2 + 1 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
      refine OMA.ne_of_cc _ ?_
      simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, constantCoeff_X]
      norm_num
    exact mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (pow_ne_zero _ X_ne_zero) h3)
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hc1 hc1)

theorem OMA.solution : type_of% @OMA.S_oeis_a128096.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hexp : C (-2176 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (6616 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-2352 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (2088 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (-6704 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (2264 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A)))
      + C (17186 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A))
      + C (-52057 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A))
      + C (22448 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A))
      + C (-10247 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A))
      + C (45764 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A))
      + C (-15333 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ OMA.A))
      + C (37525 : ℚ) * (X ^ 1 * OMA.A)
      + C (-45458 : ℚ) * (X ^ 2 * OMA.A)
      + C (24681 : ℚ) * (X ^ 3 * OMA.A)
      + C (-71306 : ℚ) * (X ^ 4 * OMA.A)
      + C (20065 : ℚ) * (X ^ 5 * OMA.A)
      = C (31530 : ℚ) * X ^ 5 + C (-7800 : ℚ) * X ^ 6 + C (3090 : ℚ) * X ^ 7 := by
    have h := OMA.ode
    simp only [map_neg, map_ofNat, map_one]
    linear_combination h
  have hc := congrArg (coeff (k + 10)) hexp
  have s0 : coeff (k + 10) (C (-2176 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-2176 : ℚ) * (((k + 10 : ℕ) : ℚ) * (((k + 10 : ℕ) : ℚ) * coeff (k + 10) OMA.A)) :=
    OMA.cXtt _ 0 _ (k + 10) _ (by omega)
  have s1 : coeff (k + 10) (C (6616 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (6616 : ℚ) * (((k + 9 : ℕ) : ℚ) * (((k + 9 : ℕ) : ℚ) * coeff (k + 9) OMA.A)) :=
    OMA.cXtt _ 1 _ (k + 9) _ (by omega)
  have s2 : coeff (k + 10) (C (-2352 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-2352 : ℚ) * (((k + 8 : ℕ) : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A)) :=
    OMA.cXtt _ 2 _ (k + 8) _ (by omega)
  have s3 : coeff (k + 10) (C (2088 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (2088 : ℚ) * (((k + 7 : ℕ) : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A)) :=
    OMA.cXtt _ 3 _ (k + 7) _ (by omega)
  have s4 : coeff (k + 10) (C (-6704 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (-6704 : ℚ) * (((k + 6 : ℕ) : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A)) :=
    OMA.cXtt _ 4 _ (k + 6) _ (by omega)
  have s5 : coeff (k + 10) (C (2264 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ (X * d⁄dX ℚ OMA.A))))
      = (2264 : ℚ) * (((k + 5 : ℕ) : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A)) :=
    OMA.cXtt _ 5 _ (k + 5) _ (by omega)
  have t0 : coeff (k + 10) (C (17186 : ℚ) * (X ^ 0 * (X * d⁄dX ℚ OMA.A)))
      = (17186 : ℚ) * (((k + 10 : ℕ) : ℚ) * coeff (k + 10) OMA.A) :=
    OMA.cXt _ 0 _ (k + 10) _ (by omega)
  have t1 : coeff (k + 10) (C (-52057 : ℚ) * (X ^ 1 * (X * d⁄dX ℚ OMA.A)))
      = (-52057 : ℚ) * (((k + 9 : ℕ) : ℚ) * coeff (k + 9) OMA.A) :=
    OMA.cXt _ 1 _ (k + 9) _ (by omega)
  have t2 : coeff (k + 10) (C (22448 : ℚ) * (X ^ 2 * (X * d⁄dX ℚ OMA.A)))
      = (22448 : ℚ) * (((k + 8 : ℕ) : ℚ) * coeff (k + 8) OMA.A) :=
    OMA.cXt _ 2 _ (k + 8) _ (by omega)
  have t3 : coeff (k + 10) (C (-10247 : ℚ) * (X ^ 3 * (X * d⁄dX ℚ OMA.A)))
      = (-10247 : ℚ) * (((k + 7 : ℕ) : ℚ) * coeff (k + 7) OMA.A) :=
    OMA.cXt _ 3 _ (k + 7) _ (by omega)
  have t4 : coeff (k + 10) (C (45764 : ℚ) * (X ^ 4 * (X * d⁄dX ℚ OMA.A)))
      = (45764 : ℚ) * (((k + 6 : ℕ) : ℚ) * coeff (k + 6) OMA.A) :=
    OMA.cXt _ 4 _ (k + 6) _ (by omega)
  have t5 : coeff (k + 10) (C (-15333 : ℚ) * (X ^ 5 * (X * d⁄dX ℚ OMA.A)))
      = (-15333 : ℚ) * (((k + 5 : ℕ) : ℚ) * coeff (k + 5) OMA.A) :=
    OMA.cXt _ 5 _ (k + 5) _ (by omega)
  have f1 : coeff (k + 10) (C (37525 : ℚ) * (X ^ 1 * OMA.A))
      = (37525 : ℚ) * coeff (k + 9) OMA.A := OMA.cXf _ 1 _ (k + 9) _ (by omega)
  have f2 : coeff (k + 10) (C (-45458 : ℚ) * (X ^ 2 * OMA.A))
      = (-45458 : ℚ) * coeff (k + 8) OMA.A := OMA.cXf _ 2 _ (k + 8) _ (by omega)
  have f3 : coeff (k + 10) (C (24681 : ℚ) * (X ^ 3 * OMA.A))
      = (24681 : ℚ) * coeff (k + 7) OMA.A := OMA.cXf _ 3 _ (k + 7) _ (by omega)
  have f4 : coeff (k + 10) (C (-71306 : ℚ) * (X ^ 4 * OMA.A))
      = (-71306 : ℚ) * coeff (k + 6) OMA.A := OMA.cXf _ 4 _ (k + 6) _ (by omega)
  have f5 : coeff (k + 10) (C (20065 : ℚ) * (X ^ 5 * OMA.A))
      = (20065 : ℚ) * coeff (k + 5) OMA.A := OMA.cXf _ 5 _ (k + 5) _ (by omega)
  have z5 : coeff (k + 10) (C (31530 : ℚ) * X ^ 5 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 5 _ (by omega)
  have z6 : coeff (k + 10) (C (-7800 : ℚ) * X ^ 6 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 6 _ (by omega)
  have z7 : coeff (k + 10) (C (3090 : ℚ) * X ^ 7 : ℚ⟦X⟧) = 0 := OMA.cX0 _ 7 _ (by omega)
  simp only [map_add, map_zero, s0, s1, s2, s3, s4, s5, t0, t1, t2, t3, t4, t5, f1, f2, f3, f4, f5, z5, z6, z7] at hc
  have e0 : a (k + 6) = coeff (k + 10) OMA.A := by
    have h : k + 6 + 4 = k + 10 := by omega
    rw [OMA.a_eq, h]
  have e1 : a (k + 6 - 1) = coeff (k + 9) OMA.A := by
    have h : k + 6 - 1 + 4 = k + 9 := by omega
    rw [OMA.a_eq, h]
  have e2 : a (k + 6 - 2) = coeff (k + 8) OMA.A := by
    have h : k + 6 - 2 + 4 = k + 8 := by omega
    rw [OMA.a_eq, h]
  have e3 : a (k + 6 - 3) = coeff (k + 7) OMA.A := by
    have h : k + 6 - 3 + 4 = k + 7 := by omega
    rw [OMA.a_eq, h]
  have e4 : a (k + 6 - 4) = coeff (k + 6) OMA.A := by
    have h : k + 6 - 4 + 4 = k + 6 := by omega
    rw [OMA.a_eq, h]
  have e5 : a (k + 6 - 5) = coeff (k + 5) OMA.A := by
    have h : k + 6 - 5 + 4 = k + 5 := by omega
    rw [OMA.a_eq, h]
  rw [e0, e1, e2, e3, e4, e5]
  push_cast at hc ⊢
  linear_combination (1 / 1 : ℚ) * hc
