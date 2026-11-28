import OMAStatements.S_oeis_a158826

namespace OMA.P158826

namespace Poly
open Polynomial

/-- The polynomial with `x = Fp(G)`. -/
noncomputable def Fp : Polynomial ℤ := (0 + X * (1 + X * ((-3) + X * (6 + X * ((-9) + X * (10
    + X * ((-8) + X * (4 + X * (-1)))))))))

/-- Derivative number 1 of `Fp`. -/
noncomputable def U0 : Polynomial ℤ := (1 + X * ((-6) + X * (18 + X * ((-36) + X * (50 + X
    * ((-48) + X * (28 + X * (-8))))))))

/-- Derivative number 2 of `Fp`. -/
noncomputable def U1 : Polynomial ℤ := ((-6) + X * (36 + X * ((-108) + X * (200 + X * ((-240)
    + X * (168 + X * (-56)))))))

/-- Derivative number 3 of `Fp`. -/
noncomputable def U2 : Polynomial ℤ := (36 + X * ((-216) + X * (600 + X * ((-960) + X * (840 + X
    * (-336))))))

/-- Derivative number 4 of `Fp`. -/
noncomputable def U3 : Polynomial ℤ := ((-216) + X * (1200 + X * ((-2880) + X * (3360 + X
    * (-1680)))))

lemma dFp : derivative Fp = U0 := by
  unfold Fp U0
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero]
  ring

lemma dU0 : derivative U0 = U1 := by
  unfold U0 U1
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero]
  ring

lemma dU1 : derivative U1 = U2 := by
  unfold U1 U2
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero]
  ring

lemma dU2 : derivative U2 = U3 := by
  unfold U2 U3
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero]
  ring

/-- Auxiliary polynomial. -/
noncomputable def P2 : Polynomial ℤ :=
  -Fp * Fp * U1 + Fp * U0 * U0

/-- Auxiliary polynomial. -/
noncomputable def P2d : Polynomial ℤ :=
  -Fp * Fp * U2 + U0 * U0 * U0

/-- Auxiliary polynomial. -/
noncomputable def P2dd : Polynomial ℤ :=
  -Fp * Fp * U3 - 2 * (Fp * U0 * U2) + 3 * (U0 * U0 * U1)

lemma dP2 : derivative P2 = P2d := by
  unfold P2 P2d
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2]
  ring

lemma dP2d : derivative P2d = P2dd := by
  unfold P2d P2dd
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2]
  ring

/-- Auxiliary polynomial. -/
noncomputable def P3 : Polynomial ℤ :=
  -Fp * Fp * Fp * U0 * U2 + 3 * (Fp * Fp * Fp * U1 * U1) - 3 * (Fp * Fp * U0 * U0 * U1) + Fp
      * U0 * U0 * U0 * U0

/-- Auxiliary polynomial. -/
noncomputable def P3d : Polynomial ℤ :=
  -Fp * Fp * Fp * U0 * U3 + 5 * (Fp * Fp * Fp * U1 * U2) - 6 * (Fp * Fp * U0 * U0 * U2) + 3
      * (Fp * Fp * U0 * U1 * U1) - 2 * (Fp * U0 * U0 * U0 * U1) + U0 * U0 * U0 * U0 * U0

lemma dP3 : derivative P3 = P3d := by
  unfold P3 P3d
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2]
  ring

/-- Auxiliary polynomial. -/
noncomputable def P4 : Polynomial ℤ :=
  -Fp * Fp * Fp * Fp * U0 * U0 * U3 + 10 * (Fp * Fp * Fp * Fp * U0 * U1 * U2) - 15 * (Fp * Fp
      * Fp * Fp * U1 * U1 * U1) - 6 * (Fp * Fp * Fp * U0 * U0 * U0 * U2) + 18 * (Fp * Fp * Fp
      * U0 * U0 * U1 * U1) - 7 * (Fp * Fp * U0 * U0 * U0 * U0 * U1) + Fp * U0 * U0 * U0 * U0
      * U0 * U0

lemma P2_eq : P2 = Fp * (U0 * U0 - 1 * (U1 * Fp)) := by
  unfold P2
  ring

lemma P3_eq : P3 = Fp * (P2d * U0 - 3 * (U1 * P2)) := by
  unfold P3 P2d P2
  ring

lemma P4_eq : P4 = Fp * (P3d * U0 - 5 * (U1 * P3)) := by
  unfold P4 P3d P3
  ring

lemma key :
    ((-6960) * Fp ^ 4 + (3840) * Fp ^ 5) * X * U0 ^ 7
      + ((-6318) * Fp ^ 0 + (52776) * Fp ^ 1 + (-145080) * Fp ^ 2 + (167320) * Fp ^ 3 + (-52352)
          * Fp ^ 4 + (16384) * Fp ^ 5) * Fp * U0 ^ 6
      + ((11583) * Fp ^ 0 + (-124812) * Fp ^ 1 + (424344) * Fp ^ 2 + (-582320) * Fp ^ 3
          + (643840) * Fp ^ 4 + (-229376) * Fp ^ 5) * P2 * U0 ^ 4
      + ((-6318) * Fp ^ 0 + (94860) * Fp ^ 1 + (-470448) * Fp ^ 2 + (738176) * Fp ^ 3 + (382976)
          * Fp ^ 4 + (-1048576) * Fp ^ 5) * P3 * U0 ^ 2
      + ((1053) * Fp ^ 0 + (-22824) * Fp ^ 1 + (191184) * Fp ^ 2 + (-769024) * Fp ^ 3
          + (1470464) * Fp ^ 4 + (-1048576) * Fp ^ 5) * P4
      = ((-3480) * Fp ^ 4 + (1920) * Fp ^ 5) * U0 ^ 7 := by
  unfold P4 P3 P2
  unfold Fp U0 U1 U2 U3
  ring

end Poly

open PowerSeries

lemma coeff_theta (H : ℤ⟦X⟧) (k : ℕ) :
    coeff k (X * d⁄dX ℤ H) = (k : ℤ) * coeff k H := by
  cases k with
  | zero => simp
  | succ j =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma step (w U V : ℤ⟦X⟧) (hw : w * U = 1) (hDw : d⁄dX ℤ w = -(w ^ 3 * V)) (m : ℕ)
    (c : ℤ⟦X⟧) (hc : c = ((m + 1 : ℕ) : ℤ⟦X⟧)) (A B Tk : ℤ⟦X⟧) (hT : Tk = A * w ^ (m + 1))
    (hA : d⁄dX ℤ A = B * w) :
    X * d⁄dX ℤ Tk = X * (B * U - c * (V * A)) * w ^ (m + 3) := by
  subst hc
  rw [hT, Derivation.leibniz, Derivation.leibniz_pow, hA, hDw]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  push_cast
  linear_combination (-(X * B * w ^ (m + 2))) * hw

open OMA.S_oeis_a158826

/-- The Catalan generating function over the integers. -/
noncomputable def Cz : ℤ⟦X⟧ := PowerSeries.mk (fun n => (catalan n : ℤ))

lemma Cz_eq : Cz = 1 + X * (Cz * Cz) := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  have e : PowerSeries.map (Nat.castRingHom ℤ) catalanSeries = Cz := by
    ext n
    simp [catalanSeries, Cz]
  simp only [map_add, map_mul, map_pow, PowerSeries.map_X, map_one, e] at h
  linear_combination -h

lemma f_eq : f = X + f * f := by
  have h : f = X * Cz := rfl
  rw [h]
  linear_combination X * Cz_eq

lemma f_const : constantCoeff f = 0 := by
  have h : f = X * Cz := rfl
  rw [h]
  simp

lemma subst_f (g : ℤ⟦X⟧) (hg : constantCoeff g = 0) :
    PowerSeries.subst g f = g + PowerSeries.subst g f * PowerSeries.subst g f := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have h := congrArg (PowerSeries.subst g) f_eq
  rw [subst_add hs, subst_mul hs, subst_X hs] at h
  exact h

/-- The second iteration. -/
noncomputable def G2 : ℤ⟦X⟧ := PowerSeries.subst f f

/-- The third iteration. -/
noncomputable def G : ℤ⟦X⟧ := PowerSeries.subst G2 f

lemma G2_const : constantCoeff G2 = 0 :=
  constantCoeff_subst_eq_zero f_const f f_const

lemma G2_eq : G2 = f + G2 * G2 := subst_f f f_const

lemma G_eq : G = G2 + G * G := subst_f G2 G2_const

lemma hX : Polynomial.aeval G Poly.Fp = X := by
  have e : Poly.Fp = ((Polynomial.X - Polynomial.X * Polynomial.X)
      - (Polynomial.X - Polynomial.X * Polynomial.X) * (Polynomial.X - Polynomial.X * Polynomial.X))
      - ((Polynomial.X - Polynomial.X * Polynomial.X)
      - (Polynomial.X - Polynomial.X * Polynomial.X) * (Polynomial.X - Polynomial.X * Polynomial.X))
      * ((Polynomial.X - Polynomial.X * Polynomial.X)
      - (Polynomial.X - Polynomial.X * Polynomial.X) * (Polynomial.X - Polynomial.X * Polynomial.X))
      := by
    unfold Poly.Fp
    ring
  rw [e]
  simp only [map_sub, map_mul, Polynomial.aeval_X]
  have h3 : G - G * G = G2 := by linear_combination G_eq
  have h2 : G2 - G2 * G2 = f := by linear_combination G2_eq
  have h1 : f - f * f = X := by linear_combination f_eq
  rw [h3, h2, h1]


/-- The derivative of the series `G`. -/
noncomputable def w : ℤ⟦X⟧ := d⁄dX ℤ G

lemma daeval (p : Polynomial ℤ) :
    d⁄dX ℤ (Polynomial.aeval G p) = Polynomial.aeval G (Polynomial.derivative p) * w := by
  rw [Derivation.map_aeval, smul_eq_mul]
  rfl

lemma hw : w * Polynomial.aeval G Poly.U0 = 1 := by
  have h := congrArg (d⁄dX ℤ) hX
  rw [daeval, Poly.dFp, derivative_X] at h
  linear_combination h

lemma hDw : d⁄dX ℤ w = -(w ^ 3 * Polynomial.aeval G Poly.U1) := by
  have h := congrArg (d⁄dX ℤ) hw
  rw [Derivation.leibniz, daeval, Poly.dU0] at h
  simp only [smul_eq_mul, Derivation.map_one_eq_zero] at h
  linear_combination (-(d⁄dX ℤ w)) * hw + w * h

/-- `T1 = theta G`, with coefficients `n * g(n)`. -/
noncomputable def T1 : ℤ⟦X⟧ := X * d⁄dX ℤ G

/-- `T2 = theta T1`. -/
noncomputable def T2 : ℤ⟦X⟧ := X * d⁄dX ℤ T1

/-- `T3 = theta T2`. -/
noncomputable def T3 : ℤ⟦X⟧ := X * d⁄dX ℤ T2

/-- `T4 = theta T3`. -/
noncomputable def T4 : ℤ⟦X⟧ := X * d⁄dX ℤ T3

lemma cT1 (k : ℕ) : coeff k T1 = (k : ℤ) * coeff k G := by
  unfold T1
  rw [coeff_theta]

lemma cT2 (k : ℕ) : coeff k T2 = (k : ℤ) ^ 2 * coeff k G := by
  unfold T2
  rw [coeff_theta, cT1]
  ring

lemma cT3 (k : ℕ) : coeff k T3 = (k : ℤ) ^ 3 * coeff k G := by
  unfold T3
  rw [coeff_theta, cT2]
  ring

lemma cT4 (k : ℕ) : coeff k T4 = (k : ℤ) ^ 4 * coeff k G := by
  unfold T4
  rw [coeff_theta, cT3]
  ring

lemma hT1 : T1 = X * w ^ 1 := by
  unfold T1 w
  ring

lemma hT2 : T2 = Polynomial.aeval G Poly.P2 * w ^ 3 := by
  have h := step w _ _ hw hDw 0 1 (by norm_num) X (Polynomial.aeval G Poly.U0) T1 hT1
    (by rw [derivative_X]; linear_combination -hw)
  unfold T2
  rw [Poly.P2_eq]
  simp only [map_mul, map_sub, map_ofNat, map_one, hX]
  linear_combination h

lemma hT3 : T3 = Polynomial.aeval G Poly.P3 * w ^ 5 := by
  have h := step w _ _ hw hDw 2 3 (by norm_num) _ _ T2 hT2
    (by rw [daeval, Poly.dP2])
  unfold T3
  rw [Poly.P3_eq]
  simp only [map_mul, map_sub, map_ofNat, map_one, hX]
  linear_combination h

lemma hT4 : T4 = Polynomial.aeval G Poly.P4 * w ^ 7 := by
  have h := step w _ _ hw hDw 4 5 (by norm_num) _ _ T3 hT3
    (by rw [daeval, Poly.dP3])
  unfold T4
  rw [Poly.P4_eq]
  simp only [map_mul, map_sub, map_ofNat, map_one, hX]
  linear_combination h

lemma ode_ring :
    ((-6960) * X ^ 4 + (3840) * X ^ 5) * G
      + ((-6318) * X ^ 0 + (52776) * X ^ 1 + (-145080) * X ^ 2 + (167320) * X ^ 3 + (-52352)
          * X ^ 4 + (16384) * X ^ 5) * T1
      + ((11583) * X ^ 0 + (-124812) * X ^ 1 + (424344) * X ^ 2 + (-582320) * X ^ 3 + (643840)
          * X ^ 4 + (-229376) * X ^ 5) * T2
      + ((-6318) * X ^ 0 + (94860) * X ^ 1 + (-470448) * X ^ 2 + (738176) * X ^ 3 + (382976)
          * X ^ 4 + (-1048576) * X ^ 5) * T3
      + ((1053) * X ^ 0 + (-22824) * X ^ 1 + (191184) * X ^ 2 + (-769024) * X ^ 3 + (1470464)
          * X ^ 4 + (-1048576) * X ^ 5) * T4
      = ((-3480) * X ^ 4 + (1920) * X ^ 5) := by
  have hk := congrArg (Polynomial.aeval G) Poly.key
  simp only [map_add, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    Polynomial.aeval_X, hX] at hk
  have hw1 := hw
  rw [hT1, hT2, hT3, hT4]
  generalize Polynomial.aeval G Poly.U0 = U at hk hw1
  generalize Polynomial.aeval G Poly.P2 = A2 at hk ⊢
  generalize Polynomial.aeval G Poly.P3 = A3 at hk ⊢
  generalize Polynomial.aeval G Poly.P4 = A4 at hk ⊢
  linear_combination (w ^ 7) * hk
    + (-(((-6960) * X ^ 4 + (3840) * X ^ 5) * G * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w
        * U) ^ 3 + (w * U) ^ 4 + (w * U) ^ 5 + (w * U) ^ 6)
      + ((-6318) * X ^ 0 + (52776) * X ^ 1 + (-145080) * X ^ 2 + (167320) * X ^ 3 + (-52352)
          * X ^ 4 + (16384) * X ^ 5) * X * w * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w
          * U) ^ 3 + (w * U) ^ 4 + (w * U) ^ 5)
      + ((11583) * X ^ 0 + (-124812) * X ^ 1 + (424344) * X ^ 2 + (-582320) * X ^ 3 + (643840)
          * X ^ 4 + (-229376) * X ^ 5) * A2 * w ^ 3 * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2
          + (w * U) ^ 3)
      + ((-6318) * X ^ 0 + (94860) * X ^ 1 + (-470448) * X ^ 2 + (738176) * X ^ 3 + (382976)
          * X ^ 4 + (-1048576) * X ^ 5) * A3 * w ^ 5 * ((w * U) ^ 0 + (w * U) ^ 1))
      + ((-3480) * X ^ 4 + (1920) * X ^ 5) * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w
          * U) ^ 3 + (w * U) ^ 4 + (w * U) ^ 5 + (w * U) ^ 6)) * hw1

lemma ode :
    C (-6960 : ℤ) * (X * (X * (X * (X * G))))
      + C (3840 : ℤ) * (X * (X * (X * (X * (X * G)))))
      + C (-6318 : ℤ) * T1
      + C (52776 : ℤ) * (X * T1)
      + C (-145080 : ℤ) * (X * (X * T1))
      + C (167320 : ℤ) * (X * (X * (X * T1)))
      + C (-52352 : ℤ) * (X * (X * (X * (X * T1))))
      + C (16384 : ℤ) * (X * (X * (X * (X * (X * T1)))))
      + C (11583 : ℤ) * T2
      + C (-124812 : ℤ) * (X * T2)
      + C (424344 : ℤ) * (X * (X * T2))
      + C (-582320 : ℤ) * (X * (X * (X * T2)))
      + C (643840 : ℤ) * (X * (X * (X * (X * T2))))
      + C (-229376 : ℤ) * (X * (X * (X * (X * (X * T2)))))
      + C (-6318 : ℤ) * T3
      + C (94860 : ℤ) * (X * T3)
      + C (-470448 : ℤ) * (X * (X * T3))
      + C (738176 : ℤ) * (X * (X * (X * T3)))
      + C (382976 : ℤ) * (X * (X * (X * (X * T3))))
      + C (-1048576 : ℤ) * (X * (X * (X * (X * (X * T3)))))
      + C (1053 : ℤ) * T4
      + C (-22824 : ℤ) * (X * T4)
      + C (191184 : ℤ) * (X * (X * T4))
      + C (-769024 : ℤ) * (X * (X * (X * T4)))
      + C (1470464 : ℤ) * (X * (X * (X * (X * T4))))
      + C (-1048576 : ℤ) * (X * (X * (X * (X * (X * T4)))))
      = C (-3480 : ℤ) * X ^ 4 + C (1920 : ℤ) * X ^ 5 := by
  simp only [map_neg, map_ofNat, map_one]
  linear_combination ode_ring

lemma rec_raw (m : ℕ) :
    coeff (m + 6) (C (-6960 : ℤ) * (X * (X * (X * (X * G))))
      + C (3840 : ℤ) * (X * (X * (X * (X * (X * G)))))
      + C (-6318 : ℤ) * T1
      + C (52776 : ℤ) * (X * T1)
      + C (-145080 : ℤ) * (X * (X * T1))
      + C (167320 : ℤ) * (X * (X * (X * T1)))
      + C (-52352 : ℤ) * (X * (X * (X * (X * T1))))
      + C (16384 : ℤ) * (X * (X * (X * (X * (X * T1)))))
      + C (11583 : ℤ) * T2
      + C (-124812 : ℤ) * (X * T2)
      + C (424344 : ℤ) * (X * (X * T2))
      + C (-582320 : ℤ) * (X * (X * (X * T2)))
      + C (643840 : ℤ) * (X * (X * (X * (X * T2))))
      + C (-229376 : ℤ) * (X * (X * (X * (X * (X * T2)))))
      + C (-6318 : ℤ) * T3
      + C (94860 : ℤ) * (X * T3)
      + C (-470448 : ℤ) * (X * (X * T3))
      + C (738176 : ℤ) * (X * (X * (X * T3)))
      + C (382976 : ℤ) * (X * (X * (X * (X * T3))))
      + C (-1048576 : ℤ) * (X * (X * (X * (X * (X * T3)))))
      + C (1053 : ℤ) * T4
      + C (-22824 : ℤ) * (X * T4)
      + C (191184 : ℤ) * (X * (X * T4))
      + C (-769024 : ℤ) * (X * (X * (X * T4)))
      + C (1470464 : ℤ) * (X * (X * (X * (X * T4))))
      + C (-1048576 : ℤ) * (X * (X * (X * (X * (X * T4)))))) = 0 := by
  rw [ode]
  simp only [map_add, coeff_C_mul, coeff_X_pow]
  simp

lemma rec (m : ℕ) :
    1053 * ((m : ℤ) + 6) * ((m : ℤ) + 5) * ((m : ℤ) + 4) * ((m : ℤ) + 3) * coeff (m + 6) G
      - 36 * ((m : ℤ) + 5) * ((m : ℤ) + 4) * ((m : ℤ) + 3) * (634 * ((m : ℤ) + 6) - 1367)
        * coeff (m + 5) G
      + 24 * ((m : ℤ) + 4) * ((m : ℤ) + 3)
        * (7966 * ((m : ℤ) + 6) ^ 2 - 43500 * ((m : ℤ) + 6) + 61181) * coeff (m + 4) G
      - 8 * ((m : ℤ) + 3) * (96128 * ((m : ℤ) + 6) ^ 3 - 957424 * ((m : ℤ) + 6) ^ 2
          + 3221878 * ((m : ℤ) + 6) - 3665189) * coeff (m + 3) G
      + 16 * (91904 * ((m : ℤ) + 6) ^ 4 - 1446528 * ((m : ℤ) + 6) ^ 3
          + 8575792 * ((m : ℤ) + 6) ^ 2 - 22703688 * ((m : ℤ) + 6) + 22652013) * coeff (m + 2) G
      - 256 * (8 * ((m : ℤ) + 6) - 35) * (8 * ((m : ℤ) + 6) - 41) * (8 * ((m : ℤ) + 6) - 39)
        * (8 * ((m : ℤ) + 6) - 37) * coeff (m + 1) G = 0 := by
  have h := rec_raw m
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cT1, cT2, cT3, cT4] at h
  push_cast at h
  linear_combination h

end OMA.P158826

open OMA.S_oeis_a158826 OMA.P158826 in
theorem OMA.solution : type_of% @OMA.S_oeis_a158826.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  have h := rec m
  have ha : ∀ k, a k = PowerSeries.coeff k G := fun k => rfl
  simp only [ha]
  push_cast
  linear_combination h
