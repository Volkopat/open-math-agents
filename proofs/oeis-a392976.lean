import OMAStatements.S_oeis_a392976

namespace OMA.P392976

namespace Poly
open Polynomial

/-- The polynomial with `x = Fp(G)`. -/
noncomputable def Fp : Polynomial ℤ := (0 + X * (1 + X * ((-1) + X * ((-2) + X * (0 + X * 1)))))

/-- Derivative number 1 of `Fp`. -/
noncomputable def U0 : Polynomial ℤ := (1 + X * ((-2) + X * ((-6) + X * (0 + X * 5))))

/-- Derivative number 2 of `Fp`. -/
noncomputable def U1 : Polynomial ℤ := ((-2) + X * ((-12) + X * (0 + X * 20)))

/-- Derivative number 3 of `Fp`. -/
noncomputable def U2 : Polynomial ℤ := ((-12) + X * (0 + X * 60))

/-- Derivative number 4 of `Fp`. -/
noncomputable def U3 : Polynomial ℤ := (0 + X * 120)

/-- Derivative number 5 of `Fp`. -/
noncomputable def U4 : Polynomial ℤ := 120

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

lemma dU3 : derivative U3 = U4 := by
  unfold U3 U4
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

/-- Auxiliary polynomial. -/
noncomputable def P2ddd : Polynomial ℤ :=
  -Fp * Fp * U4 - 4 * (Fp * U0 * U3) - 2 * (Fp * U1 * U2) + U0 * U0 * U2 + 6 * (U0 * U1 * U1)

lemma dP2 : derivative P2 = P2d := by
  unfold P2 P2d
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2, dU3]
  ring

lemma dP2d : derivative P2d = P2dd := by
  unfold P2d P2dd
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2, dU3]
  ring

lemma dP2dd : derivative P2dd = P2ddd := by
  unfold P2dd P2ddd
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2, dU3]
  ring

/-- Auxiliary polynomial. -/
noncomputable def P3 : Polynomial ℤ :=
  -Fp * Fp * Fp * U0 * U2 + 3 * (Fp * Fp * Fp * U1 * U1) - 3 * (Fp * Fp * U0 * U0 * U1) + Fp
      * U0 * U0 * U0 * U0

/-- Auxiliary polynomial. -/
noncomputable def P3d : Polynomial ℤ :=
  -Fp * Fp * Fp * U0 * U3 + 5 * (Fp * Fp * Fp * U1 * U2) - 6 * (Fp * Fp * U0 * U0 * U2) + 3
      * (Fp * Fp * U0 * U1 * U1) - 2 * (Fp * U0 * U0 * U0 * U1) + U0 * U0 * U0 * U0 * U0

/-- Auxiliary polynomial. -/
noncomputable def P3dd : Polynomial ℤ :=
  -Fp * Fp * Fp * U0 * U4 + 4 * (Fp * Fp * Fp * U1 * U3) + 5 * (Fp * Fp * Fp * U2 * U2) - 9
      * (Fp * Fp * U0 * U0 * U3) + 9 * (Fp * Fp * U0 * U1 * U2) + 3 * (Fp * Fp * U1 * U1 * U1)
      - 14 * (Fp * U0 * U0 * U0 * U2) + 3 * (U0 * U0 * U0 * U0 * U1)

lemma dP3 : derivative P3 = P3d := by
  unfold P3 P3d
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2, dU3]
  ring

lemma dP3d : derivative P3d = P3dd := by
  unfold P3d P3dd
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2, dU3]
  ring

/-- Auxiliary polynomial. -/
noncomputable def P4 : Polynomial ℤ :=
  -Fp * Fp * Fp * Fp * U0 * U0 * U3 + 10 * (Fp * Fp * Fp * Fp * U0 * U1 * U2) - 15 * (Fp * Fp
      * Fp * Fp * U1 * U1 * U1) - 6 * (Fp * Fp * Fp * U0 * U0 * U0 * U2) + 18 * (Fp * Fp * Fp
      * U0 * U0 * U1 * U1) - 7 * (Fp * Fp * U0 * U0 * U0 * U0 * U1) + Fp * U0 * U0 * U0 * U0
      * U0 * U0

/-- Auxiliary polynomial. -/
noncomputable def P4d : Polynomial ℤ :=
  -Fp * Fp * Fp * Fp * U0 * U0 * U4 + 8 * (Fp * Fp * Fp * Fp * U0 * U1 * U3) + 10 * (Fp * Fp
      * Fp * Fp * U0 * U2 * U2) - 35 * (Fp * Fp * Fp * Fp * U1 * U1 * U2) - 10 * (Fp * Fp * Fp
      * U0 * U0 * U0 * U3) + 58 * (Fp * Fp * Fp * U0 * U0 * U1 * U2) - 24 * (Fp * Fp * Fp * U0
      * U1 * U1 * U1) - 25 * (Fp * Fp * U0 * U0 * U0 * U0 * U2) + 26 * (Fp * Fp * U0 * U0 * U0
      * U1 * U1) - 8 * (Fp * U0 * U0 * U0 * U0 * U0 * U1) + U0 * U0 * U0 * U0 * U0 * U0 * U0

lemma dP4 : derivative P4 = P4d := by
  unfold P4 P4d
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_ofNat,
    derivative_neg, derivative_one, derivative_zero,
    dFp, dU0, dU1, dU2, dU3]
  ring

/-- Auxiliary polynomial. -/
noncomputable def P5 : Polynomial ℤ :=
  -Fp * Fp * Fp * Fp * Fp * U0 * U0 * U0 * U4 + 15 * (Fp * Fp * Fp * Fp * Fp * U0 * U0 * U1
      * U3) + 10 * (Fp * Fp * Fp * Fp * Fp * U0 * U0 * U2 * U2) - 105 * (Fp * Fp * Fp * Fp * Fp
      * U0 * U1 * U1 * U2) + 105 * (Fp * Fp * Fp * Fp * Fp * U1 * U1 * U1 * U1) - 10 * (Fp * Fp
      * Fp * Fp * U0 * U0 * U0 * U0 * U3) + 100 * (Fp * Fp * Fp * Fp * U0 * U0 * U0 * U1 * U2)
      - 150 * (Fp * Fp * Fp * Fp * U0 * U0 * U1 * U1 * U1) - 25 * (Fp * Fp * Fp * U0 * U0 * U0
      * U0 * U0 * U2) + 75 * (Fp * Fp * Fp * U0 * U0 * U0 * U0 * U1 * U1) - 15 * (Fp * Fp * U0
      * U0 * U0 * U0 * U0 * U0 * U1) + Fp * U0 * U0 * U0 * U0 * U0 * U0 * U0 * U0

lemma P2_eq : P2 = Fp * (U0 * U0 - 1 * (U1 * Fp)) := by
  unfold P2
  ring

lemma P3_eq : P3 = Fp * (P2d * U0 - 3 * (U1 * P2)) := by
  unfold P3 P2d P2
  ring

lemma P4_eq : P4 = Fp * (P3d * U0 - 5 * (U1 * P3)) := by
  unfold P4 P3d P3
  ring

lemma P5_eq : P5 = Fp * (P4d * U0 - 7 * (U1 * P4)) := by
  unfold P5 P4d P4
  ring

lemma key :
    ((22498755364440) * Fp ^ 4 + (-1783830606240) * Fp ^ 5) * X * U0 ^ 9
      + ((443869704406506) * Fp ^ 0 + (-631696696084332) * Fp ^ 1 + (150303090946488) * Fp ^ 2
          + (-47328111063336) * Fp ^ 3 + (76280596048590) * Fp ^ 4 + (-8783208787100) * Fp ^ 5)
          * Fp * U0 ^ 8
      + ((-954732998996935) * Fp ^ 0 + (1488868655358738) * Fp ^ 1 + (-694672635940308) * Fp ^ 2
          + (-163835111692148) * Fp ^ 3 + (-491148614566025) * Fp ^ 4 + (31535715708750)
          * Fp ^ 5) * P2 * U0 ^ 6
      + ((702318140534575) * Fp ^ 0 + (-1274195207740074) * Fp ^ 1 + (274811398608282) * Fp ^ 2
          + (1725431414053694) * Fp ^ 3 + (-1970549502499625) * Fp ^ 4 + (213952797756250)
          * Fp ^ 5) * P3 * U0 ^ 4
      + ((-214950158319425) * Fp ^ 0 + (490203969890442) * Fp ^ 1 + (676304124913800) * Fp ^ 2
          + (-1956656367732778) * Fp ^ 3 + (-1656815253836875) * Fp ^ 4 + (326501236181250)
          * Fp ^ 5) * P4 * U0 ^ 2
      + ((23495312375279) * Fp ^ 0 + (-73180721424774) * Fp ^ 1 + (-406745978528262) * Fp ^ 2
          + (-384334715888720) * Fp ^ 3 + (78200611484375) * Fp ^ 4 + (140685548031250)
          * Fp ^ 5) * P5
      = 0 * U0 ^ 9 := by
  unfold P5 P4 P3 P2
  unfold Fp U0 U1 U2 U3 U4
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

open OMA.S_oeis_a392976

/-- The series reversion. -/
noncomputable def G : ℤ⟦X⟧ := R

lemma P_const : constantCoeff P = 0 := by
  unfold P
  simp

lemma hX : Polynomial.aeval G Poly.Fp = X := by
  have hs : HasSubst G := HasSubst.substInvOfIsUnit P _
  have h : PowerSeries.subst G P = X := subst_substInvOfIsUnit_right P P_const _
  unfold P at h
  rw [← coe_substAlgHom hs] at h
  simp only [map_mul, map_sub, map_pow, map_one, substAlgHom_X] at h
  have e : Poly.Fp = Polynomial.X * ((1 - Polynomial.X ^ 2) ^ 2 - Polynomial.X) := by
    unfold Poly.Fp
    ring
  rw [e]
  simp only [map_mul, map_sub, map_pow, map_one, Polynomial.aeval_X]
  exact h


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

/-- `T5 = theta T4`. -/
noncomputable def T5 : ℤ⟦X⟧ := X * d⁄dX ℤ T4

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

lemma cT5 (k : ℕ) : coeff k T5 = (k : ℤ) ^ 5 * coeff k G := by
  unfold T5
  rw [coeff_theta, cT4]
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

lemma hT5 : T5 = Polynomial.aeval G Poly.P5 * w ^ 9 := by
  have h := step w _ _ hw hDw 6 7 (by norm_num) _ _ T4 hT4
    (by rw [daeval, Poly.dP4])
  unfold T5
  rw [Poly.P5_eq]
  simp only [map_mul, map_sub, map_ofNat, map_one, hX]
  linear_combination h

lemma ode_ring :
    ((22498755364440) * X ^ 4 + (-1783830606240) * X ^ 5) * G
      + ((443869704406506) * X ^ 0 + (-631696696084332) * X ^ 1 + (150303090946488) * X ^ 2
          + (-47328111063336) * X ^ 3 + (76280596048590) * X ^ 4 + (-8783208787100) * X ^ 5) * T1
      + ((-954732998996935) * X ^ 0 + (1488868655358738) * X ^ 1 + (-694672635940308) * X ^ 2
          + (-163835111692148) * X ^ 3 + (-491148614566025) * X ^ 4 + (31535715708750) * X ^ 5) * T2
      + ((702318140534575) * X ^ 0 + (-1274195207740074) * X ^ 1 + (274811398608282) * X ^ 2
          + (1725431414053694) * X ^ 3 + (-1970549502499625) * X ^ 4 + (213952797756250)
          * X ^ 5) * T3
      + ((-214950158319425) * X ^ 0 + (490203969890442) * X ^ 1 + (676304124913800) * X ^ 2
          + (-1956656367732778) * X ^ 3 + (-1656815253836875) * X ^ 4 + (326501236181250)
          * X ^ 5) * T4
      + ((23495312375279) * X ^ 0 + (-73180721424774) * X ^ 1 + (-406745978528262) * X ^ 2
          + (-384334715888720) * X ^ 3 + (78200611484375) * X ^ 4 + (140685548031250) * X ^ 5) * T5
      = 0 := by
  have hk := congrArg (Polynomial.aeval G) Poly.key
  simp only [map_add, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    Polynomial.aeval_X, hX] at hk
  have hw1 := hw
  rw [hT1, hT2, hT3, hT4, hT5]
  generalize Polynomial.aeval G Poly.U0 = U at hk hw1
  generalize Polynomial.aeval G Poly.P2 = A2 at hk ⊢
  generalize Polynomial.aeval G Poly.P3 = A3 at hk ⊢
  generalize Polynomial.aeval G Poly.P4 = A4 at hk ⊢
  generalize Polynomial.aeval G Poly.P5 = A5 at hk ⊢
  linear_combination (w ^ 9) * hk
    + (-(((22498755364440) * X ^ 4 + (-1783830606240) * X ^ 5) * G * ((w * U) ^ 0 + (w * U) ^ 1
        + (w * U) ^ 2 + (w * U) ^ 3 + (w * U) ^ 4 + (w * U) ^ 5 + (w * U) ^ 6 + (w * U) ^ 7 + (w
        * U) ^ 8)
      + ((443869704406506) * X ^ 0 + (-631696696084332) * X ^ 1 + (150303090946488) * X ^ 2
          + (-47328111063336) * X ^ 3 + (76280596048590) * X ^ 4 + (-8783208787100) * X ^ 5) * X
          * w * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w * U) ^ 3 + (w * U) ^ 4 + (w
          * U) ^ 5 + (w * U) ^ 6 + (w * U) ^ 7)
      + ((-954732998996935) * X ^ 0 + (1488868655358738) * X ^ 1 + (-694672635940308) * X ^ 2
          + (-163835111692148) * X ^ 3 + (-491148614566025) * X ^ 4 + (31535715708750) * X ^ 5)
          * A2 * w ^ 3 * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w * U) ^ 3 + (w * U) ^ 4
          + (w * U) ^ 5)
      + ((702318140534575) * X ^ 0 + (-1274195207740074) * X ^ 1 + (274811398608282) * X ^ 2
          + (1725431414053694) * X ^ 3 + (-1970549502499625) * X ^ 4 + (213952797756250)
          * X ^ 5) * A3 * w ^ 5 * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w * U) ^ 3)
      + ((-214950158319425) * X ^ 0 + (490203969890442) * X ^ 1 + (676304124913800) * X ^ 2
          + (-1956656367732778) * X ^ 3 + (-1656815253836875) * X ^ 4 + (326501236181250)
          * X ^ 5) * A4 * w ^ 7 * ((w * U) ^ 0 + (w * U) ^ 1))
      + 0 * ((w * U) ^ 0 + (w * U) ^ 1 + (w * U) ^ 2 + (w * U) ^ 3 + (w * U) ^ 4 + (w * U) ^ 5
          + (w * U) ^ 6 + (w * U) ^ 7 + (w * U) ^ 8)) * hw1

lemma ode :
    C (22498755364440 : ℤ) * (X * (X * (X * (X * G))))
      + C (-1783830606240 : ℤ) * (X * (X * (X * (X * (X * G)))))
      + C (443869704406506 : ℤ) * T1
      + C (-631696696084332 : ℤ) * (X * T1)
      + C (150303090946488 : ℤ) * (X * (X * T1))
      + C (-47328111063336 : ℤ) * (X * (X * (X * T1)))
      + C (76280596048590 : ℤ) * (X * (X * (X * (X * T1))))
      + C (-8783208787100 : ℤ) * (X * (X * (X * (X * (X * T1)))))
      + C (-954732998996935 : ℤ) * T2
      + C (1488868655358738 : ℤ) * (X * T2)
      + C (-694672635940308 : ℤ) * (X * (X * T2))
      + C (-163835111692148 : ℤ) * (X * (X * (X * T2)))
      + C (-491148614566025 : ℤ) * (X * (X * (X * (X * T2))))
      + C (31535715708750 : ℤ) * (X * (X * (X * (X * (X * T2)))))
      + C (702318140534575 : ℤ) * T3
      + C (-1274195207740074 : ℤ) * (X * T3)
      + C (274811398608282 : ℤ) * (X * (X * T3))
      + C (1725431414053694 : ℤ) * (X * (X * (X * T3)))
      + C (-1970549502499625 : ℤ) * (X * (X * (X * (X * T3))))
      + C (213952797756250 : ℤ) * (X * (X * (X * (X * (X * T3)))))
      + C (-214950158319425 : ℤ) * T4
      + C (490203969890442 : ℤ) * (X * T4)
      + C (676304124913800 : ℤ) * (X * (X * T4))
      + C (-1956656367732778 : ℤ) * (X * (X * (X * T4)))
      + C (-1656815253836875 : ℤ) * (X * (X * (X * (X * T4))))
      + C (326501236181250 : ℤ) * (X * (X * (X * (X * (X * T4)))))
      + C (23495312375279 : ℤ) * T5
      + C (-73180721424774 : ℤ) * (X * T5)
      + C (-406745978528262 : ℤ) * (X * (X * T5))
      + C (-384334715888720 : ℤ) * (X * (X * (X * T5)))
      + C (78200611484375 : ℤ) * (X * (X * (X * (X * T5))))
      + C (140685548031250 : ℤ) * (X * (X * (X * (X * (X * T5)))))
      = 0 := by
  simp only [map_neg, map_ofNat, map_one]
  linear_combination ode_ring

lemma rec_raw (m : ℕ) :
    coeff (m + 6) (C (22498755364440 : ℤ) * (X * (X * (X * (X * G))))
      + C (-1783830606240 : ℤ) * (X * (X * (X * (X * (X * G)))))
      + C (443869704406506 : ℤ) * T1
      + C (-631696696084332 : ℤ) * (X * T1)
      + C (150303090946488 : ℤ) * (X * (X * T1))
      + C (-47328111063336 : ℤ) * (X * (X * (X * T1)))
      + C (76280596048590 : ℤ) * (X * (X * (X * (X * T1))))
      + C (-8783208787100 : ℤ) * (X * (X * (X * (X * (X * T1)))))
      + C (-954732998996935 : ℤ) * T2
      + C (1488868655358738 : ℤ) * (X * T2)
      + C (-694672635940308 : ℤ) * (X * (X * T2))
      + C (-163835111692148 : ℤ) * (X * (X * (X * T2)))
      + C (-491148614566025 : ℤ) * (X * (X * (X * (X * T2))))
      + C (31535715708750 : ℤ) * (X * (X * (X * (X * (X * T2)))))
      + C (702318140534575 : ℤ) * T3
      + C (-1274195207740074 : ℤ) * (X * T3)
      + C (274811398608282 : ℤ) * (X * (X * T3))
      + C (1725431414053694 : ℤ) * (X * (X * (X * T3)))
      + C (-1970549502499625 : ℤ) * (X * (X * (X * (X * T3))))
      + C (213952797756250 : ℤ) * (X * (X * (X * (X * (X * T3)))))
      + C (-214950158319425 : ℤ) * T4
      + C (490203969890442 : ℤ) * (X * T4)
      + C (676304124913800 : ℤ) * (X * (X * T4))
      + C (-1956656367732778 : ℤ) * (X * (X * (X * T4)))
      + C (-1656815253836875 : ℤ) * (X * (X * (X * (X * T4))))
      + C (326501236181250 : ℤ) * (X * (X * (X * (X * (X * T4)))))
      + C (23495312375279 : ℤ) * T5
      + C (-73180721424774 : ℤ) * (X * T5)
      + C (-406745978528262 : ℤ) * (X * (X * T5))
      + C (-384334715888720 : ℤ) * (X * (X * (X * T5)))
      + C (78200611484375 : ℤ) * (X * (X * (X * (X * T5))))
      + C (140685548031250 : ℤ) * (X * (X * (X * (X * (X * T5)))))) = 0 := by
  rw [ode, map_zero]

lemma rec (m : ℕ) :
    283 * ((m : ℤ) + 5) * (((m : ℤ) + 5) - 1) * (((m : ℤ) + 5) - 2) * (83022305213 * ((m : ℤ)
        + 5) - 178385058984) * (((m : ℤ) + 5) + 1) * coeff (m + 6) G
      - 6 * ((m : ℤ) + 5) * (((m : ℤ) + 5) - 1) * (((m : ℤ) + 5) - 2)
        * (12196786904129 * ((m : ℤ) + 5) ^ 2 - 45110300936020 * ((m : ℤ) + 5) + 52641391340361)
            * coeff (m + 5) G
      - 6 * (((m : ℤ) + 5) - 1) * (((m : ℤ) + 5) - 2) * (67790996421377 * ((m : ℤ) + 5) ^ 3
          - 248299346995054 * ((m : ℤ) + 5) ^ 2
          + 202497447227007 * ((m : ℤ) + 5) + 3061418504418) * coeff (m + 4) G
      - 2 * (((m : ℤ) + 5) - 2) * (192167357944360 * ((m : ℤ) + 5) ^ 4 - 559010679688491
          * ((m : ℤ) + 5) ^ 3
          - 2120668219560541 * ((m : ℤ) + 5) ^ 2 + 9123363136130610 * ((m : ℤ) + 5)
              - 8342981628089220) * coeff (m + 3) G
      + 5 * (15640122296875 * ((m : ℤ) + 5) ^ 5 - 565964885220500 * ((m : ℤ) + 5) ^ 4
          + 4989857715427325 * ((m : ℤ) + 5) ^ 3
          - 18667678380008380 * ((m : ℤ) + 5) ^ 2 + 32085126156301848 * ((m : ℤ) + 5)
              - 20925325629575136) * coeff (m + 2) G
      + 10 * (5 * ((m : ℤ) + 5) - 17) * (5 * ((m : ℤ) + 5) - 18) * (5 * ((m : ℤ) + 5) - 21) * (5
          * ((m : ℤ) + 5) - 19)
        * (22509687685 * ((m : ℤ) + 5) - 60308240636) * coeff (m + 1) G = 0 := by
  have h := rec_raw m
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, cT1, cT2, cT3, cT4, cT5] at h
  push_cast at h
  linear_combination h

end OMA.P392976

open OMA.S_oeis_a392976 OMA.P392976 in
theorem OMA.solution : type_of% @OMA.S_oeis_a392976.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 4 := by omega
  have e2 : m + 5 - 2 = m + 3 := by omega
  have e3 : m + 5 - 3 = m + 2 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  have e5 : m + 5 - 5 = m := by omega
  rw [e1, e2, e3, e4, e5]
  have h := rec m
  have ha : ∀ k, a k = PowerSeries.coeff (k + 1) G := fun k => rfl
  simp only [ha]
  push_cast
  linear_combination h
