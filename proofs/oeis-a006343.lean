import OMAStatements.S_oeis_a006343

-- Problem: A006343: Arkons: number of elementary maps with n-1 nodes.
-- Upstream: formal-conjectures statements/oeis-a006343.lean:0 (declaration OMA.S_oeis_a006343.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A006343Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-2 + X : ℚ⟦X⟧) * G + (1 - X : ℚ⟦X⟧) * G ^ 2 + (X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (-X ^ 2 + 11 * X ^ 3 - 37 * X ^ 4 + 29 * X ^ 5 + 61 * X ^ 6 - 155 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-3 * X + 31 * X ^ 2 - 103 * X ^ 3 + 78 * X ^ 4 + 260 * X ^ 5 - 620 * X ^ 6) * derivative ℚ G + (3 - 36 * X + 103 * X ^ 2 - 36 * X ^ 3 + 138 * X ^ 4 - 310 * X ^ 5) * G =
      3 - 36 * X + 98 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (1 : ℚ⟦X⟧) + (-2 + 1 * X : ℚ⟦X⟧) * G + (1 - 1 * X : ℚ⟦X⟧) * G * G + (1 * (X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (-2 + 1 * X : ℚ⟦X⟧) * G + (1 - 1 * X : ℚ⟦X⟧) * G * G + (1 * (X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-2 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 - 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (-2 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 - 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-2 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 - 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G * G + (3 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (3 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-2 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 - 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G * G + (3 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (3 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-2 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 2 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (18 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hd2 : (-2 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 2 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (18 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-2 + X : ℚ⟦X⟧) + (2 - 2 * X : ℚ⟦X⟧) * G + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((-X ^ 2 + 11 * X ^ 3 - 37 * X ^ 4 + 29 * X ^ 5 + 61 * X ^ 6 - 155 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-3 * X + 31 * X ^ 2 - 103 * X ^ 3 + 78 * X ^ 4 + 260 * X ^ 5 - 620 * X ^ 6) * derivative ℚ G + (3 - 36 * X + 103 * X ^ 2 - 36 * X ^ 3 + 138 * X ^ 4 - 310 * X ^ 5) * G - (3 - 36 * X + 98 * X ^ 2)) = 0 := by
    linear_combination ((24 - 324 * X + 1234 * X ^ 2 - 1395 * X ^ 3 + 624 * X ^ 4 - 98 * X ^ 5 : ℚ⟦X⟧) + (-48 + 672 * X - 2784 * X ^ 2 + 4014 * X ^ 3 - 3288 * X ^ 4 + 3408 * X ^ 5 - 1230 * X ^ 6 : ℚ⟦X⟧) * G + (24 - 348 * X + 1554 * X ^ 2 - 2802 * X ^ 3 + 4410 * X ^ 4 - 8904 * X ^ 5 + 6534 * X ^ 6 - 1218 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (144 * X ^ 3 - 1764 * X ^ 4 + 6372 * X ^ 5 - 6768 * X ^ 6 + 2016 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (108 * X ^ 6 - 1215 * X ^ 7 + 3564 * X ^ 8 - 1512 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-12 * X + 132 * X ^ 2 - 493 * X ^ 3 + 585 * X ^ 4 + 815 * X ^ 5 - 3256 * X ^ 6 + 1998 * X ^ 7 - 310 * X ^ 8 : ℚ⟦X⟧) + (-4 * X ^ 2 + 50 * X ^ 3 - 216 * X ^ 4 + 360 * X ^ 5 - 4 * X ^ 6 - 928 * X ^ 7 + 1052 * X ^ 8 - 310 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (24 * X - 274 * X ^ 2 + 1092 * X ^ 3 - 1548 * X ^ 4 - 1244 * X ^ 5 + 7332 * X ^ 6 - 6564 * X ^ 7 + 1550 * X ^ 8 : ℚ⟦X⟧) * G + (4 * X ^ 2 - 52 * X ^ 3 + 240 * X ^ 4 - 468 * X ^ 5 + 274 * X ^ 6 + 482 * X ^ 7 - 914 * X ^ 8 + 1178 * X ^ 9 - 2226 * X ^ 10 + 930 * X ^ 11 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * X + 142 * X ^ 2 - 600 * X ^ 3 + 972 * X ^ 4 + 424 * X ^ 5 - 4164 * X ^ 6 + 4860 * X ^ 7 - 2528 * X ^ 8 + 2322 * X ^ 9 - 930 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (18 * X ^ 5 - 216 * X ^ 6 + 864 * X ^ 7 - 1188 * X ^ 8 - 576 * X ^ 9 + 3888 * X ^ 10 - 2790 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-6 * X ^ 4 + 42 * X ^ 5 - 102 * X ^ 6 - 30 * X ^ 7 + 1398 * X ^ 8 - 3714 * X ^ 9 + 1860 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (18 * X ^ 8 - 198 * X ^ 9 + 666 * X ^ 10 - 522 * X ^ 11 - 1098 * X ^ 12 + 2790 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (9 * X ^ 7 - 117 * X ^ 8 + 405 * X ^ 9 - 342 * X ^ 10 + 144 * X ^ 11 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((-4 * X ^ 2 + 48 * X ^ 3 - 193 * X ^ 4 + 275 * X ^ 5 + 91 * X ^ 6 - 835 * X ^ 7 + 681 * X ^ 8 - 155 * X ^ 9 : ℚ⟦X⟧) + (8 * X ^ 2 - 100 * X ^ 3 + 432 * X ^ 4 - 720 * X ^ 5 + 8 * X ^ 6 + 1856 * X ^ 7 - 2104 * X ^ 8 + 620 * X ^ 9 : ℚ⟦X⟧) * G + (-4 * X ^ 2 + 52 * X ^ 3 - 240 * X ^ 4 + 468 * X ^ 5 - 274 * X ^ 6 - 482 * X ^ 7 + 914 * X ^ 8 - 1178 * X ^ 9 + 2226 * X ^ 10 - 930 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (-12 * X ^ 5 + 144 * X ^ 6 - 576 * X ^ 7 + 792 * X ^ 8 + 384 * X ^ 9 - 2592 * X ^ 10 + 1860 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (-9 * X ^ 8 + 99 * X ^ 9 - 333 * X ^ 10 + 261 * X ^ 11 + 549 * X ^ 12 - 1395 * X ^ 13 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hres : ((18 - 45 * X + 36 * X ^ 2 + 108 * X ^ 3 - 117 * X ^ 4 + 36 * X ^ 5 : ℚ⟦X⟧) + (-18 + 54 * X - 54 * X ^ 2 - 108 * X ^ 3 + 189 * X ^ 4 - 63 * X ^ 5 - 81 * X ^ 6 : ℚ⟦X⟧) * G + (-18 * X ^ 3 + 36 * X ^ 4 - 18 * X ^ 5 - 108 * X ^ 6 + 54 * X ^ 7 : ℚ⟦X⟧) * G ^ 2) * ((-2 + X : ℚ⟦X⟧) + (2 - 2 * X : ℚ⟦X⟧) * G + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) = (-9 * X ^ 2 + 54 * X ^ 3 - 63 * X ^ 4 - 54 * X ^ 5 + 279 * X ^ 6 : ℚ⟦X⟧) := by
    linear_combination (-((36 - 108 * X + 108 * X ^ 2 + 234 * X ^ 3 - 405 * X ^ 4 + 135 * X ^ 5 + 243 * X ^ 6 : ℚ⟦X⟧) + (54 * X ^ 3 - 108 * X ^ 4 + 54 * X ^ 5 + 324 * X ^ 6 - 162 * X ^ 7 : ℚ⟦X⟧) * G)) * hP
  have hd0 : (-9 + 54 * X - 63 * X ^ 2 - 54 * X ^ 3 + 279 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (9 : ℚ⟦X⟧) = 9 := cnum 9
    simp [kc] at h'
  have hdisc : (-9 * X ^ 2 + 54 * X ^ 3 - 63 * X ^ 4 - 54 * X ^ 5 + 279 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-9 * X ^ 2 + 54 * X ^ 3 - 63 * X ^ 4 - 54 * X ^ 5 + 279 * X ^ 6 : ℚ⟦X⟧) = X ^ 2 * (-9 + 54 * X - 63 * X ^ 2 - 54 * X ^ 3 + 279 * X ^ 4 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hd0
  have hPG : (-2 + X : ℚ⟦X⟧) + (2 - 2 * X : ℚ⟦X⟧) * G + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-2 + X : ℚ⟦X⟧) * G + (1 - X : ℚ⟦X⟧) * G ^ 2 + (X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    derivative ℚ (derivative ℚ G) * X * X * C (-1) + derivative ℚ (derivative ℚ G) * X * X * X * C 11 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-37) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 29 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 61 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-155) +
      derivative ℚ G * X * C (-3) + derivative ℚ G * X * X * C 31 +
      derivative ℚ G * X * X * X * C (-103) + derivative ℚ G * X * X * X * X * C 78 +
      derivative ℚ G * X * X * X * X * X * C 260 + derivative ℚ G * X * X * X * X * X * X * C (-620) +
      G * C 3 + G * X * C (-36) +
      G * X * X * C 103 + G * X * X * X * C (-36) +
      G * X * X * X * X * C 138 + G * X * X * X * X * X * C (-310) =
      C 3 + C (-36) * X +
      C 98 * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-2 + X : ℚ⟦X⟧) * G + (1 - X : ℚ⟦X⟧) * G ^ 2 + (X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) (m : ℕ) :
    (-1) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 11 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-37) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 29 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      61 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-155) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-3) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 31 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-103) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 78 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      260 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-620) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      3 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-36) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      103 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-36) * coeff (m + 1 + 1 + 1 + 1) G +
      138 * coeff (m + 1 + 1 + 1) G + (-310) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-2 + X : ℚ⟦X⟧) * G + (1 - X : ℚ⟦X⟧) * G ^ 2 + (X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (-20) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 132 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-222) * coeff (0 + 1 + 1 + 1) G + 58 * coeff (0 + 1 + 1) G +
      (-15) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 124 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-309) * coeff (0 + 1 + 1 + 1) G + 156 * coeff (0 + 1 + 1) G +
      260 * coeff (0 + 1) G + 3 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1 + 1 + 1) G + 103 * coeff (0 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1) G + 138 * coeff (0 + 1) G +
      (-310) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-2 + X : ℚ⟦X⟧) * G + (1 - X : ℚ⟦X⟧) * G ^ 2 + (X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (-30) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 220 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-444) * coeff (0 + 1 + 1 + 1 + 1) G + 174 * coeff (0 + 1 + 1 + 1) G +
      122 * coeff (0 + 1 + 1) G + (-18) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      155 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-412) * coeff (0 + 1 + 1 + 1 + 1) G +
      234 * coeff (0 + 1 + 1 + 1) G + 520 * coeff (0 + 1 + 1) G +
      (-620) * coeff (0 + 1) G + 3 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 103 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1 + 1) G + 138 * coeff (0 + 1 + 1) G +
      (-310) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A006343Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a006343.main := by
  intro G hG _ _ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  have hP : (1 : PowerSeries ℚ) + (-2 + PowerSeries.X : PowerSeries ℚ) * G + (1 - PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination hG
  cases m with
  | zero =>
    have r := A006343Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A006343Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A006343Aux.rel G hP m
      push_cast
      linear_combination r
