import OMAStatements.S_oeis_a128743

-- Problem: A128743: Number of UU's (i.e., doublerises) in all skew Dyck paths of semilength n.
-- Upstream: formal-conjectures statements/oeis-a128743.lean:0 (declaration OMA.S_oeis_a128743.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A128743Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) :
    (16 * X - 160 * X ^ 2 + 480 * X ^ 3 - 416 * X ^ 4 + 80 * X ^ 5) * derivative ℚ G + (16 - 144 * X + 336 * X ^ 2 - 272 * X ^ 3) * G = 96 * X ^ 2 - 96 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d22 : derivative ℚ (22 : ℚ⟦X⟧) = 0 := dnum 22
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hS2 : S * S = (1 - 6 * X + 5 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 2 + 24 * X ^ 3 - 20 * X ^ 4) * G = (2 * X - 14 * X ^ 2 + 22 * X ^ 3 - 10 * X ^ 4 : ℚ⟦X⟧) + (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) * S := by
    linear_combination (0 - (2 * X) * S) * hG + (2 * X) * ((2 * X) * G - (-1 + X)) * hS
  have hPd : derivative ℚ (1 - 6 * X + 5 * (X * X) : ℚ⟦X⟧) = -6 + 10 * X := by
    simp [Derivation.leibniz, d5, d6]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -6 + 10 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X) + 24 * (X * X * X) - 20 * (X * X * X * X) : ℚ⟦X⟧) * G) = (-8 * X + 72 * X ^ 2 - 80 * X ^ 3) * G + (-4 * X ^ 2 + 24 * X ^ 3 - 20 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d20, d24]
    ring
  have hR : derivative ℚ ((2 * X - 14 * (X * X) + 22 * (X * X * X) - 10 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 8 * (X * X) - 2 * (X * X * X) : ℚ⟦X⟧) * S) =
      2 - 28 * X + 66 * X ^ 2 - 40 * X ^ 3 + (-2 + 16 * X - 6 * X ^ 2) * S + (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d8, d10, d14, d22]
    ring
  have hk2 : (-4 * (X * X) + 24 * (X * X * X) - 20 * (X * X * X * X) : ℚ⟦X⟧) * G = (2 * X - 14 * (X * X) + 22 * (X * X * X) - 10 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 8 * (X * X) - 2 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X + 72 * X ^ 2 - 80 * X ^ 3) * G + (-4 * X ^ 2 + 24 * X ^ 3 - 20 * X ^ 4) * derivative ℚ G =
      2 - 28 * X + 66 * X ^ 2 - 40 * X ^ 3 + (-2 + 16 * X - 6 * X ^ 2) * S + (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 6 * X + 5 * X ^ 2) * ((16 * X - 160 * X ^ 2 + 480 * X ^ 3 - 416 * X ^ 4 + 80 * X ^ 5) * derivative ℚ G + (16 - 144 * X + 336 * X ^ 2 - 272 * X ^ 3) * G - (96 * X ^ 2 - 96 * X ^ 3))) = 0 := by
    linear_combination (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) ^ 2 * S * hdS - 2 * (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 + 16 * X - 6 * X ^ 2) * (1 - 6 * X + 5 * X ^ 2) + (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) * (-6 + 10 * X)) * hk + 2 * (-2 * X + 8 * X ^ 2 - 2 * X ^ 3) * (1 - 6 * X + 5 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 6 * X + 5 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) :
    (X ^ 3 - 6 * X ^ 4 + 5 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-15 * X ^ 3 + 25 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-2 * X + 2 * X ^ 2 + 20 * X ^ 3) * derivative ℚ G + (4) * G =
      0 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d144 : derivative ℚ (144 : ℚ⟦X⟧) = 0 := dnum 144
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d272 : derivative ℚ (272 : ℚ⟦X⟧) = 0 := dnum 272
  have d288 : derivative ℚ (288 : ℚ⟦X⟧) = 0 := dnum 288
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have d336 : derivative ℚ (336 : ℚ⟦X⟧) = 0 := dnum 336
  have d400 : derivative ℚ (400 : ℚ⟦X⟧) = 0 := dnum 400
  have d416 : derivative ℚ (416 : ℚ⟦X⟧) = 0 := dnum 416
  have d480 : derivative ℚ (480 : ℚ⟦X⟧) = 0 := dnum 480
  have d672 : derivative ℚ (672 : ℚ⟦X⟧) = 0 := dnum 672
  have d816 : derivative ℚ (816 : ℚ⟦X⟧) = 0 := dnum 816
  have d1440 : derivative ℚ (1440 : ℚ⟦X⟧) = 0 := dnum 1440
  have d1664 : derivative ℚ (1664 : ℚ⟦X⟧) = 0 := dnum 1664
  have hL : derivative ℚ ((16 * X - 160 * (X * X) + 480 * (X * X * X) - 416 * (X * X * X * X) + 80 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 144 * X + 336 * (X * X) - 272 * (X * X * X) : ℚ⟦X⟧) * G) =
      (16 - 320 * X + 1440 * X ^ 2 - 1664 * X ^ 3 + 400 * X ^ 4) * derivative ℚ G + (16 * X - 160 * X ^ 2 + 480 * X ^ 3 - 416 * X ^ 4 + 80 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-144 + 672 * X - 816 * X ^ 2) * G + (16 - 144 * X + 336 * X ^ 2 - 272 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d80, d144, d160, d272, d336, d416, d480]
    ring
  have hRd : derivative ℚ (96 * (X * X) - 96 * (X * X * X) : ℚ⟦X⟧) = 192 * X - 288 * X ^ 2 := by
    simp [Derivation.leibniz, d96]
    ring
  have h2 : (16 * X - 160 * (X * X) + 480 * (X * X * X) - 416 * (X * X * X * X) + 80 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 144 * X + 336 * (X * X) - 272 * (X * X * X) : ℚ⟦X⟧) * G = (96 * (X * X) - 96 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (16 - 320 * X + 1440 * X ^ 2 - 1664 * X ^ 3 + 400 * X ^ 4) * derivative ℚ G + (16 * X - 160 * X ^ 2 + 480 * X ^ 3 - 416 * X ^ 4 + 80 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-144 + 672 * X - 816 * X ^ 2) * G + (16 - 144 * X + 336 * X ^ 2 - 272 * X ^ 3) * derivative ℚ G = 192 * X - 288 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((16 - 320 * X + 1440 * (X * X) - 1664 * (X * X * X) + 400 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 * X - 160 * (X * X) + 480 * (X * X * X) - 416 * (X * X * X * X) + 80 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-144 + 672 * X - 816 * (X * X) : ℚ⟦X⟧) * G + (16 - 144 * X + 336 * (X * X) - 272 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-608 + 4224 * X - 6624 * X ^ 2 + 1600 * X ^ 3) * derivative ℚ G + (48 - 784 * X + 3216 * X ^ 2 - 3600 * X ^ 3 + 800 * X ^ 4) * derivative ℚ (derivative ℚ G) + (16 * X - 160 * X ^ 2 + 480 * X ^ 3 - 416 * X ^ 4 + 80 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (672 - 1632 * X) * G := by
    simp [Derivation.leibniz, d16, d80, d144, d160, d272, d320, d336, d400, d416, d480, d672, d816, d1440, d1664]
    ring
  have hRd2 : derivative ℚ (192 * X - 288 * (X * X) : ℚ⟦X⟧) = 192 - 576 * X := by
    simp [Derivation.leibniz, d192, d288]
    ring
  have hdp : (16 - 320 * X + 1440 * (X * X) - 1664 * (X * X * X) + 400 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 * X - 160 * (X * X) + 480 * (X * X * X) - 416 * (X * X * X * X) + 80 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-144 + 672 * X - 816 * (X * X) : ℚ⟦X⟧) * G + (16 - 144 * X + 336 * (X * X) - 272 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (192 * X - 288 * (X * X) : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-608 + 4224 * X - 6624 * X ^ 2 + 1600 * X ^ 3) * derivative ℚ G + (48 - 784 * X + 3216 * X ^ 2 - 3600 * X ^ 3 + 800 * X ^ 4) * derivative ℚ (derivative ℚ G) + (16 * X - 160 * X ^ 2 + 480 * X ^ 3 - 416 * X ^ 4 + 80 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (672 - 1632 * X) * G = 192 - 576 * X := by
    rw [← hL2, hdp, hRd2]
  have hfull : (16 - 128 * X + 288 * X ^ 2 - 128 * X ^ 3 + 16 * X ^ 4) * ((X ^ 3 - 6 * X ^ 4 + 5 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-15 * X ^ 3 + 25 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-2 * X + 2 * X ^ 2 + 20 * X ^ 3) * derivative ℚ G + (4) * G - (0)) = 0 := by
    linear_combination (X ^ 2 - 4 * X ^ 3 + X ^ 4) * hd2 + (-3 * X + 16 * X ^ 2 - 5 * X ^ 3) * hd + (4 - 23 * X + 9 * X ^ 2) * h
  have hg : (16 - 128 * X + 288 * X ^ 2 - 128 * X ^ 3 + 16 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-6) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 5 + derivative ℚ (derivative ℚ G) * X * X * X * C (-15) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 25 + derivative ℚ G * X * C (-2) +
      derivative ℚ G * X * X * C 2 + derivative ℚ G * X * X * X * C 20 +
      G * C 4 =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) (m : ℕ) :
    1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      5 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-15) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      25 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 20 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) :
    (-4) * coeff (0 + 1 + 1) G + 2 * coeff (0 + 1) G +
      4 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) :
    6 * coeff (0 + 1 + 1 + 1) G + (-30) * coeff (0 + 1 + 1) G +
      (-6) * coeff (0 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1) G +
      20 * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (0 + (2 * X) * S) = 1 - 4 * X + X ^ 2 + (-1 + X) * S) :
    24 * coeff (0 + 1 + 1 + 1 + 1) G + (-36) * coeff (0 + 1 + 1 + 1) G +
      (-90) * coeff (0 + 1 + 1 + 1) G + 50 * coeff (0 + 1 + 1) G +
      (-8) * coeff (0 + 1 + 1 + 1 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      40 * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A128743Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a128743.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A128743Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A128743Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A128743Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination hG)
        push_cast
        linear_combination r
      | succ m =>
        have r := A128743Aux.rel (S) G (by linear_combination hS)
            (by linear_combination hG) m
        push_cast
        linear_combination r
