import OMAStatements.S_oeis_a182899

-- Problem: A182899: Number of returns to the horizontal axis (both from above and below) in all weighted lattice paths in L_n.
-- Upstream: formal-conjectures statements/oeis-a182899.lean:0 (declaration OMA.S_oeis_a182899.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A182899Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (1 - 4 * X + 2 * X ^ 2 + 11 * X ^ 4 + 2 * X ^ 6 - 4 * X ^ 7 + X ^ 8 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (X - 4 * X ^ 2 + 2 * X ^ 3 + 11 * X ^ 5 + 2 * X ^ 7 - 4 * X ^ 8 + X ^ 9) * derivative ℚ G + (-X + X ^ 2 + 11 * X ^ 4 + 3 * X ^ 6 - 7 * X ^ 7 + 2 * X ^ 8) * G =
      6 * X ^ 3 - 2 * X ^ 4 + 2 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d11 : derivative ℚ (11 : ℚ⟦X⟧) = 0 := dnum 11
  have hp0 : (4 * (X * X * X) : ℚ⟦X⟧) + (-2 + 6 * X - 2 * (X * X * X) - 8 * (X * X * X * X) - 2 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 - 4 * X + 2 * (X * X) + 11 * (X * X * X * X) + 2 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((4 * (X * X * X) : ℚ⟦X⟧) + (-2 + 6 * X - 2 * (X * X * X) - 8 * (X * X * X * X) - 2 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 - 4 * X + 2 * (X * X) + 11 * (X * X * X * X) + 2 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (12 * X ^ 2 : ℚ⟦X⟧) + (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (6 - 6 * X ^ 2 - 32 * X ^ 3 - 10 * X ^ 4 + 12 * X ^ 5 : ℚ⟦X⟧) * G + (2 - 8 * X + 4 * X ^ 2 + 22 * X ^ 4 + 4 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-4 + 4 * X + 44 * X ^ 3 + 12 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d11]
    ring
  have hd1 : (12 * X ^ 2 : ℚ⟦X⟧) + (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (6 - 6 * X ^ 2 - 32 * X ^ 3 - 10 * X ^ 4 + 12 * X ^ 5 : ℚ⟦X⟧) * G + (2 - 8 * X + 4 * X ^ 2 + 22 * X ^ 4 + 4 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-4 + 4 * X + 44 * X ^ 3 + 12 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) + (2 - 8 * X + 4 * X ^ 2 + 22 * X ^ 4 + 4 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G) ^ 1 * ((X - 4 * X ^ 2 + 2 * X ^ 3 + 11 * X ^ 5 + 2 * X ^ 7 - 4 * X ^ 8 + X ^ 9) * derivative ℚ G + (-X + X ^ 2 + 11 * X ^ 4 + 3 * X ^ 6 - 7 * X ^ 7 + 2 * X ^ 8) * G - (6 * X ^ 3 - 2 * X ^ 4 + 2 * X ^ 5)) = 0 := by
    linear_combination ((2 * X - 2 * X ^ 2 - 22 * X ^ 4 - 6 * X ^ 6 + 14 * X ^ 7 - 4 * X ^ 8 : ℚ⟦X⟧)) * hP +
      ((X - 4 * X ^ 2 + 2 * X ^ 3 + 11 * X ^ 5 + 2 * X ^ 7 - 4 * X ^ 8 + X ^ 9 : ℚ⟦X⟧)) * hd1
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hPG : (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) + (2 - 8 * X + 4 * X ^ 2 + 22 * X ^ 4 + 4 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (1 - 4 * X + 2 * X ^ 2 + 11 * X ^ 4 + 2 * X ^ 6 - 4 * X ^ 7 + X ^ 8 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-4) +
      derivative ℚ G * X * X * X * C 2 + derivative ℚ G * X * X * X * X * X * C 11 +
      derivative ℚ G * X * X * X * X * X * X * X * C 2 + derivative ℚ G * X * X * X * X * X * X * X * X * C (-4) +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C 1 + G * X * C (-1) +
      G * X * X * C 1 + G * X * X * X * X * C 11 +
      G * X * X * X * X * X * X * C 3 + G * X * X * X * X * X * X * X * C (-7) +
      G * X * X * X * X * X * X * X * X * C 2 =
      C 6 * X * X * X + C (-2) * X * X * X * X +
      C 2 * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (1 - 4 * X + 2 * X ^ 2 + 11 * X ^ 4 + 2 * X ^ 6 - 4 * X ^ 7 + X ^ 8 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 11 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      1 * ((m : ℚ) + 1) * coeff (m + 1) G + (-1) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 11 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      3 * coeff (m + 1 + 1 + 1) G + (-7) * coeff (m + 1 + 1) G +
      2 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (-2 + 6 * X - 2 * X ^ 3 - 8 * X ^ 4 - 2 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (1 - 4 * X + 2 * X ^ 2 + 11 * X ^ 4 + 2 * X ^ 6 - 4 * X ^ 7 + X ^ 8 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    8 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-28) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 44 * coeff (0 + 1 + 1 + 1 + 1) G +
      4 * coeff (0 + 1 + 1) G + (-4) * coeff (0 + 1) G +
      (-1) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      11 * coeff (0 + 1 + 1 + 1 + 1) G + 3 * coeff (0 + 1 + 1) G +
      (-7) * coeff (0 + 1) G + 2 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A182899Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182899.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m := rfl
  rw [e1, e2, e4, e6, e7, e8]
  have kn2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 := A182899Aux.cnum 2
  have hN1 : ((1) + (-2) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 + (-2) * PowerSeries.X ^ 3 + (1) * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn2] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 3) * (((1) + (-2) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 + (-2) * PowerSeries.X ^ 3 + (1) * PowerSeries.X ^ 4) ^ 2 * ((4 * PowerSeries.X ^ 3 : PowerSeries ℚ) + (-2 + 6 * PowerSeries.X - 2 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G + (1 - 4 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + 11 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 6 - 4 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((4) * PowerSeries.X ^ 6 + (-16) * PowerSeries.X ^ 7 + (8) * PowerSeries.X ^ 8 + (44) * PowerSeries.X ^ 10 + (8) * PowerSeries.X ^ 12 + (-16) * PowerSeries.X ^ 13 + (4) * PowerSeries.X ^ 14) * hT +
      ((2) * PowerSeries.X ^ 3 + (-1) * PowerSeries.X ^ 3 * G + (-10) * PowerSeries.X ^ 4 + (6) * PowerSeries.X ^ 4 * G + (10) * PowerSeries.X ^ 5 + (-9) * PowerSeries.X ^ 5 * G + (4) * PowerSeries.X ^ 6 + (-2) * PowerSeries.X ^ 6 * T + (2) * PowerSeries.X ^ 6 * G + (18) * PowerSeries.X ^ 7 + (8) * PowerSeries.X ^ 7 * T + (-18) * PowerSeries.X ^ 7 * G + (-22) * PowerSeries.X ^ 8 + (-4) * PowerSeries.X ^ 8 * T + (30) * PowerSeries.X ^ 8 * G + (-18) * PowerSeries.X ^ 9 + (7) * PowerSeries.X ^ 9 * G + (-12) * PowerSeries.X ^ 10 + (-22) * PowerSeries.X ^ 10 * T + (30) * PowerSeries.X ^ 10 * G + (6) * PowerSeries.X ^ 11 + (-18) * PowerSeries.X ^ 11 * G + (6) * PowerSeries.X ^ 12 + (-4) * PowerSeries.X ^ 12 * T + (2) * PowerSeries.X ^ 12 * G + (-2) * PowerSeries.X ^ 13 + (8) * PowerSeries.X ^ 13 * T + (-9) * PowerSeries.X ^ 13 * G + (-2) * PowerSeries.X ^ 14 * T + (6) * PowerSeries.X ^ 14 * G + (-1) * PowerSeries.X ^ 15 * G) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 3) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 3 PowerSeries.X_ne_zero)
  have hP : (4 * PowerSeries.X ^ 3 : PowerSeries ℚ) + (-2 + 6 * PowerSeries.X - 2 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G + (1 - 4 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + 11 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 6 - 4 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A182899Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A182899Aux.rel G hP h0c m
    push_cast
    linear_combination r
