import OMAStatements.S_oeis_a055392

-- Problem: A055392: Number of bracketings of 0#0#0#...#0 giving result 0, where 0#0 = 1, 0#1 = 1#0 = 1#1 = 0.
-- Upstream: formal-conjectures statements/oeis-a055392.lean:0 (declaration OMA.S_oeis_a055392.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A055392Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (500 * X ^ 2 + 500 * X ^ 3 + 500 * X ^ 4 - 140161 * X ^ 5 + 500 * X ^ 6 + 1568576 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-200 * X ^ 2 - 6760 * X ^ 3 - 14568 * X ^ 4 - 48518 * X ^ 5 + 1568576 * X ^ 6) * derivative ℚ G + (400 * X ^ 2 + 720 * X ^ 3 + 6096 * X ^ 4 - 98036 * X ^ 5) * G =
      200 * X ^ 2 + 360 * X ^ 3 + 3048 * X ^ 4 - 49018 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hp0 : (1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d4, d6]
    ring
  have hd2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((1 : ℚ⟦X⟧) + (-6 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((500 * X ^ 2 + 500 * X ^ 3 + 500 * X ^ 4 - 140161 * X ^ 5 + 500 * X ^ 6 + 1568576 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-200 * X ^ 2 - 6760 * X ^ 3 - 14568 * X ^ 4 - 48518 * X ^ 5 + 1568576 * X ^ 6) * derivative ℚ G + (400 * X ^ 2 + 720 * X ^ 3 + 6096 * X ^ 4 - 98036 * X ^ 5) * G - (200 * X ^ 2 + 360 * X ^ 3 + 3048 * X ^ 4 - 49018 * X ^ 5)) = 0 := by
    linear_combination ((6400 * X ^ 2 + 11520 * X ^ 3 + 97536 * X ^ 4 - 1568576 * X ^ 5 : ℚ⟦X⟧) + (-4800 * X ^ 2 - 85440 * X ^ 3 - 211392 * X ^ 4 + 6000 * X ^ 5 + 18822912 * X ^ 6 : ℚ⟦X⟧) * G + (4800 * X ^ 2 + 85440 * X ^ 3 + 211392 * X ^ 4 - 6000 * X ^ 5 - 18822912 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (-25600 * X ^ 2 - 46080 * X ^ 3 - 390144 * X ^ 4 + 6274304 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 + (76800 * X ^ 2 + 138240 * X ^ 3 + 1170432 * X ^ 4 - 18822912 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (-76800 * X ^ 2 - 138240 * X ^ 3 - 1170432 * X ^ 4 + 18822912 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 + (25600 * X ^ 2 + 46080 * X ^ 3 + 390144 * X ^ 4 - 6274304 * X ^ 5 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((-200 * X ^ 2 - 6760 * X ^ 3 - 14568 * X ^ 4 - 48518 * X ^ 5 + 1568576 * X ^ 6 : ℚ⟦X⟧) + (-6000 * X ^ 2 - 6000 * X ^ 3 - 6000 * X ^ 4 + 1681932 * X ^ 5 - 6000 * X ^ 6 - 18822912 * X ^ 7 : ℚ⟦X⟧) * G + (6000 * X ^ 2 + 6000 * X ^ 3 + 6000 * X ^ 4 - 1681932 * X ^ 5 + 6000 * X ^ 6 + 18822912 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (8400 * X ^ 2 + 87120 * X ^ 3 + 180816 * X ^ 4 - 1099716 * X ^ 5 - 18816912 * X ^ 6 + 18822912 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-6000 * X ^ 2 - 6000 * X ^ 3 - 6000 * X ^ 4 + 1681932 * X ^ 5 - 6000 * X ^ 6 - 18822912 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-1600 * X ^ 2 - 54080 * X ^ 3 - 116544 * X ^ 4 - 388144 * X ^ 5 + 12548608 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (-36000 * X ^ 2 - 36000 * X ^ 3 - 36000 * X ^ 4 + 10091592 * X ^ 5 - 36000 * X ^ 6 - 112937472 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-7200 * X ^ 2 - 243360 * X ^ 3 - 524448 * X ^ 4 - 1746648 * X ^ 5 + 56468736 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (60000 * X ^ 2 + 60000 * X ^ 3 + 60000 * X ^ 4 - 16819320 * X ^ 5 + 60000 * X ^ 6 + 188229120 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (9600 * X ^ 2 + 324480 * X ^ 3 + 699264 * X ^ 4 + 2328864 * X ^ 5 - 75291648 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (-24000 * X ^ 2 - 24000 * X ^ 3 - 24000 * X ^ 4 + 6727728 * X ^ 5 - 24000 * X ^ 6 - 75291648 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-3200 * X ^ 2 - 108160 * X ^ 3 - 233088 * X ^ 4 - 776288 * X ^ 5 + 25097216 * X ^ 6 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((500 * X ^ 2 + 500 * X ^ 3 + 500 * X ^ 4 - 140161 * X ^ 5 + 500 * X ^ 6 + 1568576 * X ^ 7 : ℚ⟦X⟧) + (-6000 * X ^ 2 - 6000 * X ^ 3 - 6000 * X ^ 4 + 1681932 * X ^ 5 - 6000 * X ^ 6 - 18822912 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (4000 * X ^ 2 + 4000 * X ^ 3 + 4000 * X ^ 4 - 1121288 * X ^ 5 + 4000 * X ^ 6 + 12548608 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (18000 * X ^ 2 + 18000 * X ^ 3 + 18000 * X ^ 4 - 5045796 * X ^ 5 + 18000 * X ^ 6 + 56468736 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (-24000 * X ^ 2 - 24000 * X ^ 3 - 24000 * X ^ 4 + 6727728 * X ^ 5 - 24000 * X ^ 6 - 75291648 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 + (8000 * X ^ 2 + 8000 * X ^ 3 + 8000 * X ^ 4 - 2242576 * X ^ 5 + 8000 * X ^ 6 + 25097216 * X ^ 7 : ℚ⟦X⟧) * G ^ 6) * hd2
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have k6 : constantCoeff (6 : ℚ⟦X⟧) = 6 := cnum 6
  have hPG : (1 : ℚ⟦X⟧) + (-6 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k4, k6] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 500 + derivative ℚ (derivative ℚ G) * X * X * X * C 500 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 500 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-140161) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 500 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 1568576 +
      derivative ℚ G * X * X * C (-200) + derivative ℚ G * X * X * X * C (-6760) +
      derivative ℚ G * X * X * X * X * C (-14568) + derivative ℚ G * X * X * X * X * X * C (-48518) +
      derivative ℚ G * X * X * X * X * X * X * C 1568576 + G * X * X * C 400 +
      G * X * X * X * C 720 + G * X * X * X * X * C 6096 +
      G * X * X * X * X * X * C (-98036) =
      C 200 * X * X + C 360 * X * X * X +
      C 3048 * X * X * X * X + C (-49018) * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    500 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 500 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      500 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-140161) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      500 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 1568576 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-200) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-6760) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-14568) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-48518) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      1568576 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 400 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      720 * coeff (m + 1 + 1 + 1 + 1) G + 6096 * coeff (m + 1 + 1 + 1) G +
      (-98036) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    15000 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 10000 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      6000 * coeff (0 + 1 + 1 + 1 + 1) G + (-840966) * coeff (0 + 1 + 1 + 1) G +
      1000 * coeff (0 + 1 + 1) G + (-1000) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-27040) * coeff (0 + 1 + 1 + 1 + 1) G + (-43704) * coeff (0 + 1 + 1 + 1) G +
      (-97036) * coeff (0 + 1 + 1) G + 1568576 * coeff (0 + 1) G +
      400 * coeff (0 + 1 + 1 + 1 + 1) G + 720 * coeff (0 + 1 + 1 + 1) G +
      6096 * coeff (0 + 1 + 1) G + (-98036) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A055392Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055392.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5]
  have hn : ((2)) * ((8)) = (16 : PowerSeries ℚ) := by
    linear_combination (0 : PowerSeries ℚ) * hT
  have hnu0 : (16 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (16 : PowerSeries ℚ) = 16 := A055392Aux.cnum 16
    simp [kc] at h'
  have hnu : (16 : PowerSeries ℚ) ≠ 0 := by
    have e : (16 : PowerSeries ℚ) = PowerSeries.X ^ 0 * (16 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 0 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((2) : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((2)) ^ 4 * ((PowerSeries.X : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-2 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((4)) * hT +
      ((-3) + (1) * W ^ 2 + (-2) * T) * hW +
      ((5) + (-5) * W + (-1) * W ^ 2 + (1) * W ^ 3 + (-6) * G + (-4) * G * W + (2) * G * W ^ 2 + (-12) * G ^ 2 + (4) * G ^ 2 * W + (8) * G ^ 3) * hG
  have hP : (PowerSeries.X : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-2 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A055392Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A055392Aux.rel G hP h0c m
    push_cast
    linear_combination r
