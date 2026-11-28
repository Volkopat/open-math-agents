import OMAStatements.S_oeis_a036766

-- uses note #96692
-- Companion proof by @Heart-galaxy, published in statement PR #21536.
-- Rechecked and assembled for the registered statement, with no novelty claim.

namespace OMA.A036766Certificate

open Polynomial

noncomputable def q : ℚ[X] := 1 + X + X ^ 2 + X ^ 3 + X ^ 4

noncomputable def e : ℚ[X] := 1 - X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4

theorem e_eq : e = q - X * q.derivative := by
  simp [e, q, derivative_add]
  simp only [map_ofNat]
  ring

noncomputable def N1 : ℚ[X] := X * q * q.derivative

noncomputable def N2 : ℚ[X] := X * q * (e * N1.derivative - N1 * e.derivative)

noncomputable def N3 : ℚ[X] := X * q * (e * N2.derivative - 3 * N2 * e.derivative)

noncomputable def N4 : ℚ[X] := X * q * (e * N3.derivative - 5 * N3 * e.derivative)

-- Bk is Q^5 times the coefficient of theta^k in the shifted operator,
-- after replacing x by X / Q. The six summands are the six source lags.
noncomputable def B0 : ℚ[X] :=
  8328 * q ^ 5 - 38280 * X * q ^ 4 + 96600 * X ^ 2 * q ^ 3 -
    70500 * X ^ 3 * q ^ 2 - 1627500 * X ^ 4 * q - 12243750 * X ^ 5

noncomputable def B1 : ℚ[X] :=
  23874 * q ^ 5 - 171062 * X * q ^ 4 + 12800 * X ^ 2 * q ^ 3 -
    318875 * X ^ 3 * q ^ 2 - 4011250 * X ^ 4 * q - 25195625 * X ^ 5

noncomputable def B2 : ℚ[X] :=
  17733 * q ^ 5 - 196453 * X * q ^ 4 - 774955 * X ^ 2 * q ^ 3 -
    447425 * X ^ 3 * q ^ 2 - 3502000 * X ^ 4 * q - 17283125 * X ^ 5

noncomputable def B3 : ℚ[X] :=
  -1404 * q ^ 5 + 81098 * X * q ^ 4 - 1007030 * X ^ 2 * q ^ 3 -
    247375 * X ^ 3 * q ^ 2 - 1284875 * X ^ 4 * q - 4789375 * X ^ 5

noncomputable def B4 : ℚ[X] :=
  -3591 * q ^ 5 + 111457 * X * q ^ 4 - 342515 * X ^ 2 * q ^ 3 -
    48325 * X ^ 3 * q ^ 2 - 166625 * X ^ 4 * q - 458125 * X ^ 5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem N1_expanded :
    N1 =
    X + 3 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 10 * X ^ 5 + 9 * X ^ 6 + 7 * X ^ 7
    + 4 * X ^ 8 := by
  simp [N1, q, derivative_add]
  simp only [map_ofNat]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem N2_expanded :
    N2 =
    X + 7 * X ^ 2 + 26 * X ^ 3 + 70 * X ^ 4 + 129 * X ^ 5 + 180 * X ^ 6
    + 191 * X ^ 7 + 128 * X ^ 8 - 35 * X ^ 9 - 228 * X ^ 10 - 383 * X ^ 11
    - 448 * X ^ 12 - 404 * X ^ 13 - 285 * X ^ 14 - 151 * X ^ 15 - 48 * X ^ 16 := by
  rw [N2, N1_expanded]
  simp [q, e, derivative_add, derivative_sub, derivative_mul]
  simp only [map_ofNat]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem N3_expanded :
    N3 =
    X + 15 * X ^ 2 + 98 * X ^ 3 + 422 * X ^ 4 + 1276 * X ^ 5 + 3017 * X ^ 6
    + 5871 * X ^ 7 + 9524 * X ^ 8 + 12483 * X ^ 9 + 13097 * X ^ 10 + 10368 * X ^ 11
    + 4572 * X ^ 12 - 2360 * X ^ 13 - 6781 * X ^ 14 - 6147 * X ^ 15 - 416 * X ^ 16
    + 7933 * X ^ 17 + 15131 * X ^ 18 + 18300 * X ^ 19 + 16774 * X ^ 20
    + 12030 * X ^ 21 + 6609 * X ^ 22 + 2607 * X ^ 23 + 576 * X ^ 24 := by
  rw [N3, N2_expanded]
  simp [q, e, derivative_add, derivative_sub, derivative_mul]
  simp only [map_ofNat]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem N4_expanded :
    N4 =
    X + 31 * X ^ 2 + 334 * X ^ 3 + 2170 * X ^ 4 + 9683 * X ^ 5 + 33478 * X ^ 6
    + 95207 * X ^ 7 + 228940 * X ^ 8 + 468790 * X ^ 9 + 831945 * X ^ 10
    + 1296985 * X ^ 11 + 1782750 * X ^ 12 + 2150575 * X ^ 13 + 2280665 * X ^ 14
    + 2132240 * X ^ 15 + 1764160 * X ^ 16 + 1319110 * X ^ 17 + 970045 * X ^ 18
    + 799065 * X ^ 19 + 754530 * X ^ 20 + 702315 * X ^ 21 + 521885 * X ^ 22
    + 183880 * X ^ 23 - 226760 * X ^ 24 - 566975 * X ^ 25 - 724946 * X ^ 26
    - 680821 * X ^ 27 - 502524 * X ^ 28 - 292680 * X ^ 29 - 130173 * X ^ 30
    - 40743 * X ^ 31 - 6912 * X ^ 32 := by
  rw [N4, N3_expanded]
  simp [q, e, derivative_add, derivative_sub, derivative_mul]
  simp only [map_ofNat]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Clearing the denominators of the differential operator leaves only its initial terms. -/
theorem certificate :
    B0 * e ^ 7 * q + B1 * e ^ 6 * N1 + B2 * e ^ 4 * N2 +
      B3 * e ^ 2 * N3 + B4 * N4 = e ^ 7 * (8328 * q ^ 5 + 6660 * X * q ^ 4) := by
  rw [N1_expanded, N2_expanded, N3_expanded, N4_expanded]
  unfold B0 B1 B2 B3 B4 e q
  ring

end OMA.A036766Certificate

-- This fragment follows Certificate.lean.

namespace OMA.A036766Certificate

open Polynomial

private theorem homogenize_power {R : Type*} [CommRing R] (x y a : R)
    (hx : x * a = y) (j : ℕ) (hj : j ≤ 5) :
    a ^ 5 * x ^ j = y ^ j * a ^ (5 - j) := by
  have ha : a ^ 5 = a ^ j * a ^ (5 - j) := by
    rw [← pow_add, show j + (5 - j) = 5 by omega]
  calc
    _ = (x * a) ^ j * a ^ (5 - j) := by rw [ha, mul_pow]; ring
    _ = _ := by rw [hx]

noncomputable def op0 : ℚ[X] :=
  8328 - 38280 * X + 96600 * X ^ 2 - 70500 * X ^ 3
    - 1627500 * X ^ 4 - 12243750 * X ^ 5

theorem homogenize0 {R : Type*} [CommRing R] [Algebra ℚ R] (x y a : R)
    (hx : x * a = y) (ha : a = aeval y q) :
    a ^ 5 * aeval x op0 = aeval y B0 := by
  have h1 := homogenize_power x y a hx 1 (by decide)
  have h2 := homogenize_power x y a hx 2 (by decide)
  have h3 := homogenize_power x y a hx 3 (by decide)
  have h4 := homogenize_power x y a hx 4 (by decide)
  have h5 := homogenize_power x y a hx 5 (by decide)
  simp [op0, B0, ← ha, map_ofNat]
  linear_combination - 38280 * h1 + 96600 * h2 - 70500 * h3 - 1627500 * h4 - 12243750 * h5

noncomputable def op1 : ℚ[X] :=
  23874 - 171062 * X + 12800 * X ^ 2 - 318875 * X ^ 3
    - 4011250 * X ^ 4 - 25195625 * X ^ 5

theorem homogenize1 {R : Type*} [CommRing R] [Algebra ℚ R] (x y a : R)
    (hx : x * a = y) (ha : a = aeval y q) :
    a ^ 5 * aeval x op1 = aeval y B1 := by
  have h1 := homogenize_power x y a hx 1 (by decide)
  have h2 := homogenize_power x y a hx 2 (by decide)
  have h3 := homogenize_power x y a hx 3 (by decide)
  have h4 := homogenize_power x y a hx 4 (by decide)
  have h5 := homogenize_power x y a hx 5 (by decide)
  simp [op1, B1, ← ha, map_ofNat]
  linear_combination - 171062 * h1 + 12800 * h2 - 318875 * h3 - 4011250 * h4 - 25195625 * h5

noncomputable def op2 : ℚ[X] :=
  17733 - 196453 * X - 774955 * X ^ 2 - 447425 * X ^ 3
    - 3502000 * X ^ 4 - 17283125 * X ^ 5

theorem homogenize2 {R : Type*} [CommRing R] [Algebra ℚ R] (x y a : R)
    (hx : x * a = y) (ha : a = aeval y q) :
    a ^ 5 * aeval x op2 = aeval y B2 := by
  have h1 := homogenize_power x y a hx 1 (by decide)
  have h2 := homogenize_power x y a hx 2 (by decide)
  have h3 := homogenize_power x y a hx 3 (by decide)
  have h4 := homogenize_power x y a hx 4 (by decide)
  have h5 := homogenize_power x y a hx 5 (by decide)
  simp [op2, B2, ← ha, map_ofNat]
  linear_combination - 196453 * h1 - 774955 * h2 - 447425 * h3 - 3502000 * h4 - 17283125 * h5

noncomputable def op3 : ℚ[X] :=
  -1404 + 81098 * X - 1007030 * X ^ 2 - 247375 * X ^ 3
    - 1284875 * X ^ 4 - 4789375 * X ^ 5

theorem homogenize3 {R : Type*} [CommRing R] [Algebra ℚ R] (x y a : R)
    (hx : x * a = y) (ha : a = aeval y q) :
    a ^ 5 * aeval x op3 = aeval y B3 := by
  have h1 := homogenize_power x y a hx 1 (by decide)
  have h2 := homogenize_power x y a hx 2 (by decide)
  have h3 := homogenize_power x y a hx 3 (by decide)
  have h4 := homogenize_power x y a hx 4 (by decide)
  have h5 := homogenize_power x y a hx 5 (by decide)
  simp [op3, B3, ← ha, map_ofNat]
  linear_combination 81098 * h1 - 1007030 * h2 - 247375 * h3 - 1284875 * h4 - 4789375 * h5

noncomputable def op4 : ℚ[X] :=
  -3591 + 111457 * X - 342515 * X ^ 2 - 48325 * X ^ 3
    - 166625 * X ^ 4 - 458125 * X ^ 5

theorem homogenize4 {R : Type*} [CommRing R] [Algebra ℚ R] (x y a : R)
    (hx : x * a = y) (ha : a = aeval y q) :
    a ^ 5 * aeval x op4 = aeval y B4 := by
  have h1 := homogenize_power x y a hx 1 (by decide)
  have h2 := homogenize_power x y a hx 2 (by decide)
  have h3 := homogenize_power x y a hx 3 (by decide)
  have h4 := homogenize_power x y a hx 4 (by decide)
  have h5 := homogenize_power x y a hx 5 (by decide)
  simp [op4, B4, ← ha, map_ofNat]
  linear_combination 111457 * h1 - 342515 * h2 - 48325 * h3 - 166625 * h4 - 458125 * h5

end OMA.A036766Certificate

namespace OMA.S_oeis_a036766


noncomputable def e : Polynomial ℚ := OMA.A036766Certificate.e






noncomputable def E : PowerSeries ℚ := ev e
noncomputable def theta : Derivation ℚ (PowerSeries ℚ) (PowerSeries ℚ) :=
  (PowerSeries.X : PowerSeries ℚ) • PowerSeries.derivative ℚ
noncomputable def jet : ℕ → PowerSeries ℚ
  | 0 => A
  | n+1 => theta (jet n)

lemma Y_const : PowerSeries.constantCoeff Y = 0 := by simp [Y]
lemma Y_subst : PowerSeries.HasSubst Y := by
  unfold Y
  exact PowerSeries.HasSubst.substInvOfIsUnit _ _

lemma X_mul_A : PowerSeries.X*A = Y := by
  have hqs : PowerSeries.constantCoeff qs ≠ 0 := by simp [qs,q]
  have hF : F*qs = PowerSeries.X := by
    unfold F
    rw [mul_assoc,PowerSeries.inv_mul_cancel _ hqs,mul_one]
  have hrev : PowerSeries.subst Y F = PowerSeries.X := by
    unfold Y
    exact PowerSeries.subst_substInvOfIsUnit_right F (by simp [F]) _
  have h := congrArg (PowerSeries.subst Y) hF
  rw [PowerSeries.subst_mul Y_subst,hrev,PowerSeries.subst_X Y_subst] at h
  change PowerSeries.X*(PowerSeries.subst Y (q : PowerSeries ℚ)) = Y at h
  rw [PowerSeries.subst_coe Y_subst] at h
  exact h

lemma A_algebraic : A = 1+PowerSeries.X*A+PowerSeries.X^2*A^2+
    PowerSeries.X^3*A^3+PowerSeries.X^4*A^4 := by
  conv_lhs => unfold A ev q
  simp only [map_add,map_one,map_pow,Polynomial.aeval_X]
  rw [← X_mul_A]
  ring

lemma A_const : PowerSeries.constantCoeff A = 1 := by simp [A,ev,q,Y_const]
lemma E_const : PowerSeries.constantCoeff E = 1 := by simp [E,ev,e,OMA.A036766Certificate.e,Y_const]

lemma theta_ev (p : Polynomial ℚ) : theta (ev p) = ev p.derivative*theta Y := by
  simpa only [ev,smul_eq_mul] using theta.map_aeval p Y

lemma E_identity : E = A-Y*ev q.derivative := by
  have hq : OMA.A036766Certificate.q = q := rfl
  simp only [E,ev,e,OMA.A036766Certificate.e_eq,hq,map_sub,map_mul,Polynomial.aeval_X,A]

lemma derivative_identity : E*(PowerSeries.derivative ℚ Y) = A^2 := by
  have h := congrArg (PowerSeries.derivative ℚ) X_mul_A
  have ha : PowerSeries.derivative ℚ A = ev q.derivative*(PowerSeries.derivative ℚ Y) := by
    simpa only [A,ev,smul_eq_mul] using (PowerSeries.derivative ℚ).map_aeval q Y
  simp only [Derivation.leibniz,PowerSeries.derivative_X,smul_eq_mul,mul_one] at h
  rw [ha] at h
  rw [E_identity]
  linear_combination -A*h+(ev q.derivative)*(PowerSeries.derivative ℚ Y)*X_mul_A

lemma theta_Y : E*theta Y = Y*A := by
  change E*(PowerSeries.X*(PowerSeries.derivative ℚ Y)) = Y*A
  calc
    _ = PowerSeries.X*(E*(PowerSeries.derivative ℚ Y)) := by ring
    _ = PowerSeries.X*A^2 := by rw [derivative_identity]
    _ = Y*A := by rw [pow_two,← mul_assoc,X_mul_A]

lemma jet_step (s : ℕ) (hs : 1 ≤ s) (f : PowerSeries ℚ) (p : Polynomial ℚ)
    (h : E^s*f = ev p) :
    E^(s+2)*theta f =
      ev (Polynomial.X*q*(e*p.derivative-(s : Polynomial ℚ)*e.derivative*p)) := by
  obtain ⟨t,rfl⟩ : ∃ t : ℕ, s = t+1 := ⟨s-1,by omega⟩
  have he : theta E = ev e.derivative*theta Y := theta_ev e
  have hD := congrArg (fun v => theta v) h
  simp only [Derivation.leibniz,Derivation.leibniz_pow,nsmul_eq_mul,smul_eq_mul,
    he,theta_ev,Nat.add_sub_cancel] at hD
  have hv : ev (Polynomial.X*q*(e*p.derivative-((t+1 : ℕ) : Polynomial ℚ)*e.derivative*p)) =
      Y*A*(E*ev p.derivative-((t : PowerSeries ℚ)+1)*ev e.derivative*ev p) := by
    simp only [ev,map_mul,map_sub,Polynomial.aeval_X,map_natCast,A,E]
    push_cast
    rfl
  rw [hv]
  push_cast at hD
  linear_combination E^2*hD +
    (E*ev p.derivative-((t : PowerSeries ℚ)+1)*E^(t+1)*ev e.derivative*f)*theta_Y -
    ((t : PowerSeries ℚ)+1)*(Y*A)*ev e.derivative*h

lemma reversion_coefficient (n : ℕ) : a n = PowerSeries.coeff (n+1) Y := by
  rw [← X_mul_A,PowerSeries.coeff_succ_X_mul]
  rfl

lemma jet_one : E*jet 1 = ev OMA.A036766Certificate.N1 := by
  have hN : ev OMA.A036766Certificate.N1 = Y*A*ev q.derivative := by
    have hq : OMA.A036766Certificate.q = q := rfl
    simp only [ev,A,OMA.A036766Certificate.N1,hq,map_mul,Polynomial.aeval_X]
  change E*theta (ev q) = _
  rw [theta_ev,hN]
  linear_combination (ev q.derivative)*theta_Y

lemma jet_2 : E^3*jet 2 = ev OMA.A036766Certificate.N2 := by
  have hp : Polynomial.X*q*(e*OMA.A036766Certificate.N1.derivative-
      (1 : Polynomial ℚ)*e.derivative*OMA.A036766Certificate.N1) =
      OMA.A036766Certificate.N2 := by
    change Polynomial.X*OMA.A036766Certificate.q*(OMA.A036766Certificate.e*
      OMA.A036766Certificate.N1.derivative-(1 : Polynomial ℚ)*
      OMA.A036766Certificate.e.derivative*OMA.A036766Certificate.N1) = _
    rw [OMA.A036766Certificate.N2]
    ring
  have h := jet_step 1 (by decide) (jet 1) OMA.A036766Certificate.N1 (by simpa only [pow_one] using jet_one)
  change E^3*jet 2 = _ at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hp] at h
  exact h

lemma jet_3 : E^5*jet 3 = ev OMA.A036766Certificate.N3 := by
  have hp : Polynomial.X*q*(e*OMA.A036766Certificate.N2.derivative-
      (3 : Polynomial ℚ)*e.derivative*OMA.A036766Certificate.N2) =
      OMA.A036766Certificate.N3 := by
    change Polynomial.X*OMA.A036766Certificate.q*(OMA.A036766Certificate.e*
      OMA.A036766Certificate.N2.derivative-(3 : Polynomial ℚ)*
      OMA.A036766Certificate.e.derivative*OMA.A036766Certificate.N2) = _
    rw [OMA.A036766Certificate.N3]
    ring
  have h := jet_step 3 (by decide) (jet 2) OMA.A036766Certificate.N2 jet_2
  change E^5*jet 3 = _ at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hp] at h
  exact h

lemma jet_4 : E^7*jet 4 = ev OMA.A036766Certificate.N4 := by
  have hp : Polynomial.X*q*(e*OMA.A036766Certificate.N3.derivative-
      (5 : Polynomial ℚ)*e.derivative*OMA.A036766Certificate.N3) =
      OMA.A036766Certificate.N4 := by
    change Polynomial.X*OMA.A036766Certificate.q*(OMA.A036766Certificate.e*
      OMA.A036766Certificate.N3.derivative-(5 : Polynomial ℚ)*
      OMA.A036766Certificate.e.derivative*OMA.A036766Certificate.N3) = _
    rw [OMA.A036766Certificate.N4]
    ring
  have h := jet_step 5 (by decide) (jet 3) OMA.A036766Certificate.N3 jet_3
  change E^7*jet 4 = _ at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hp] at h
  exact h

noncomputable def L : PowerSeries ℚ :=
  Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op0*A +
  Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op1*jet 1 +
  Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op2*jet 2 +
  Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op3*jet 3 +
  Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op4*jet 4

lemma differential_equation : L = 8328+6660*PowerSeries.X := by
  have ha : A = Polynomial.aeval Y OMA.A036766Certificate.q := rfl
  have h0 := OMA.A036766Certificate.homogenize0 PowerSeries.X Y A X_mul_A ha
  change A^5*Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op0 = ev OMA.A036766Certificate.B0 at h0
  have h1 := OMA.A036766Certificate.homogenize1 PowerSeries.X Y A X_mul_A ha
  change A^5*Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op1 = ev OMA.A036766Certificate.B1 at h1
  have h2 := OMA.A036766Certificate.homogenize2 PowerSeries.X Y A X_mul_A ha
  change A^5*Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op2 = ev OMA.A036766Certificate.B2 at h2
  have h3 := OMA.A036766Certificate.homogenize3 PowerSeries.X Y A X_mul_A ha
  change A^5*Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op3 = ev OMA.A036766Certificate.B3 at h3
  have h4 := OMA.A036766Certificate.homogenize4 PowerSeries.X Y A X_mul_A ha
  change A^5*Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op4 = ev OMA.A036766Certificate.B4 at h4
  have hc := congrArg (Polynomial.aeval Y) OMA.A036766Certificate.certificate
  simp only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] at hc
  change ev OMA.A036766Certificate.B0*E^7*A +
    ev OMA.A036766Certificate.B1*E^6*ev OMA.A036766Certificate.N1 +
    ev OMA.A036766Certificate.B2*E^4*ev OMA.A036766Certificate.N2 +
    ev OMA.A036766Certificate.B3*E^2*ev OMA.A036766Certificate.N3 +
    ev OMA.A036766Certificate.B4*ev OMA.A036766Certificate.N4 =
    E^7*(8328*A^5+6660*Y*A^4) at hc
  rw [← h0,← h1,← h2,← h3,← h4,← jet_one,← jet_2,← jet_3,← jet_4] at hc
  have hnA : A ≠ 0 := by
    intro h
    have hz := congrArg PowerSeries.constantCoeff h
    simp [A_const] at hz
  have hnE : E ≠ 0 := by
    intro h
    have hz := congrArg PowerSeries.constantCoeff h
    simp [E_const] at hz
  apply mul_left_cancel₀ (a := A^5*E^7) (mul_ne_zero (pow_ne_zero 5 hnA) (pow_ne_zero 7 hnE))
  unfold L
  linear_combination hc-6660*E^7*A^4*X_mul_A

lemma coeff_theta (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (theta f) = (n : ℚ)*PowerSeries.coeff n f := by
  cases n with
  | zero => simp [theta,Derivation.smul_apply,smul_eq_mul]
  | succ n =>
    simp only [theta,Derivation.smul_apply,smul_eq_mul,PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative]
    push_cast
    ring

lemma coeff_jet (k n : ℕ) : PowerSeries.coeff n (jet k) = (n : ℚ)^k*a n := by
  induction k with
  | zero => simp [jet,a]
  | succ k ih =>
    rw [jet,coeff_theta,ih,pow_succ]
    ring

lemma coeff_A (n : ℕ) : PowerSeries.coeff n A = a n := rfl

lemma op0_eval : Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op0 =
    PowerSeries.C (8328 : ℚ)*PowerSeries.X^0 +
    PowerSeries.C (-38280 : ℚ)*PowerSeries.X^1 +
    PowerSeries.C (96600 : ℚ)*PowerSeries.X^2 +
    PowerSeries.C (-70500 : ℚ)*PowerSeries.X^3 +
    PowerSeries.C (-1627500 : ℚ)*PowerSeries.X^4 +
    PowerSeries.C (-12243750 : ℚ)*PowerSeries.X^5 := by
  simp only [OMA.A036766Certificate.op0,map_add,map_sub,map_neg,map_mul,map_pow,
    map_ofNat,Polynomial.aeval_X,pow_zero,pow_one,mul_one]
  ring

lemma op1_eval : Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op1 =
    PowerSeries.C (23874 : ℚ)*PowerSeries.X^0 +
    PowerSeries.C (-171062 : ℚ)*PowerSeries.X^1 +
    PowerSeries.C (12800 : ℚ)*PowerSeries.X^2 +
    PowerSeries.C (-318875 : ℚ)*PowerSeries.X^3 +
    PowerSeries.C (-4011250 : ℚ)*PowerSeries.X^4 +
    PowerSeries.C (-25195625 : ℚ)*PowerSeries.X^5 := by
  simp only [OMA.A036766Certificate.op1,map_add,map_sub,map_neg,map_mul,map_pow,
    map_ofNat,Polynomial.aeval_X,pow_zero,pow_one,mul_one]
  ring

lemma op2_eval : Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op2 =
    PowerSeries.C (17733 : ℚ)*PowerSeries.X^0 +
    PowerSeries.C (-196453 : ℚ)*PowerSeries.X^1 +
    PowerSeries.C (-774955 : ℚ)*PowerSeries.X^2 +
    PowerSeries.C (-447425 : ℚ)*PowerSeries.X^3 +
    PowerSeries.C (-3502000 : ℚ)*PowerSeries.X^4 +
    PowerSeries.C (-17283125 : ℚ)*PowerSeries.X^5 := by
  simp only [OMA.A036766Certificate.op2,map_sub,map_neg,map_mul,map_pow,
    map_ofNat,Polynomial.aeval_X,pow_zero,pow_one,mul_one]
  ring

lemma op3_eval : Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op3 =
    PowerSeries.C (-1404 : ℚ)*PowerSeries.X^0 +
    PowerSeries.C (81098 : ℚ)*PowerSeries.X^1 +
    PowerSeries.C (-1007030 : ℚ)*PowerSeries.X^2 +
    PowerSeries.C (-247375 : ℚ)*PowerSeries.X^3 +
    PowerSeries.C (-1284875 : ℚ)*PowerSeries.X^4 +
    PowerSeries.C (-4789375 : ℚ)*PowerSeries.X^5 := by
  simp only [OMA.A036766Certificate.op3,map_add,map_sub,map_neg,map_mul,map_pow,
    map_ofNat,Polynomial.aeval_X,pow_zero,pow_one,mul_one]
  ring

lemma op4_eval : Polynomial.aeval PowerSeries.X OMA.A036766Certificate.op4 =
    PowerSeries.C (-3591 : ℚ)*PowerSeries.X^0 +
    PowerSeries.C (111457 : ℚ)*PowerSeries.X^1 +
    PowerSeries.C (-342515 : ℚ)*PowerSeries.X^2 +
    PowerSeries.C (-48325 : ℚ)*PowerSeries.X^3 +
    PowerSeries.C (-166625 : ℚ)*PowerSeries.X^4 +
    PowerSeries.C (-458125 : ℚ)*PowerSeries.X^5 := by
  simp only [OMA.A036766Certificate.op4,map_add,map_sub,map_neg,map_mul,map_pow,
    map_ofNat,Polynomial.aeval_X,pow_zero,pow_one,mul_one]
  ring

theorem solution_lemma : ∀ n : ℕ, 5 ≤ n →
    -3*(3*(n : ℚ)+2)*(133*(n : ℚ)-347)*(3*(n : ℚ)+4)*((n : ℚ)+1)*a n +
      (111457*(n : ℚ)^4-364730*(n : ℚ)^3+228995*(n : ℚ)^2+19310*(n : ℚ)-33312)*a (n-1) +
      5*(-68503*(n : ℚ)^4+346618*(n : ℚ)^3-590627*(n : ℚ)^2+397748*(n : ℚ)-90564)*a (n-2) -
      25*((n : ℚ)-2)*(1933*(n : ℚ)^3-9435*(n : ℚ)^2+14354*(n : ℚ)-7518)*a (n-3) -
      125*((n : ℚ)-2)*((n : ℚ)-3)*(1333*(n : ℚ)^2-4384*(n : ℚ)+2718)*a (n-4) -
      625*(733*(n : ℚ)-400)*((n : ℚ)-2)*((n : ℚ)-3)*((n : ℚ)-4)*a (n-5) = 0 := by
  intro n hn
  have hd : L = PowerSeries.C 8328+PowerSeries.C 6660*PowerSeries.X := by
    simpa only [map_ofNat] using differential_equation
  have hc := congrArg (PowerSeries.coeff n) hd
  rw [L,op0_eval,op1_eval,op2_eval,op3_eval,op4_eval] at hc
  simp only [add_mul,mul_assoc,map_add,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul',coeff_jet,coeff_A,PowerSeries.coeff_C,
    PowerSeries.coeff_X,pow_zero,mul_one] at hc
  simp only [if_pos (show 1 ≤ n by omega),if_pos (show 2 ≤ n by omega),
    if_pos (show 3 ≤ n by omega),if_pos (show 4 ≤ n by omega),if_pos (show 5 ≤ n by omega),
    if_neg (show n ≠ 0 by omega),if_neg (show n ≠ 1 by omega),mul_zero,add_zero] at hc
  rw [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega),Nat.cast_sub (show 4 ≤ n by omega),
    Nat.cast_sub (show 5 ≤ n by omega)] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linear_combination hc

end OMA.S_oeis_a036766


theorem OMA.solution : type_of% @OMA.S_oeis_a036766.main := by
  exact OMA.S_oeis_a036766.solution_lemma


