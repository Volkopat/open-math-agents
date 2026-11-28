import OMAStatements.S_oeis_a138164

-- Problem: A138164: Row sums of Riordan array (c(-x^2),xc(-x^2)^2)^(-1) where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a138164.lean:0 (declaration OMA.S_oeis_a138164.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A138164Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (-8 * X ^ 2 + 12 * X ^ 3 + 178 * X ^ 4 - 381 * X ^ 5 - 741 * X ^ 6 + 2025 * X ^ 7 - 648 * X ^ 8) * derivative ℚ (derivative ℚ G) + (60 * X ^ 2 - 134 * X ^ 3 - 522 * X ^ 4 + 624 * X ^ 5 + 2268 * X ^ 6 - 1944 * X ^ 7) * derivative ℚ G + (-34 * X ^ 2 + 108 * X ^ 3 + 222 * X ^ 4 - 306 * X ^ 5 - 576 * X ^ 6) * G =
      -6 * X ^ 2 + 36 * X ^ 3 + 60 * X ^ 4 - 72 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have hp0 : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G * G + (1 - 3 * X + 1 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G * G + (1 - 3 * X + 1 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G ^ 2 + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-3 + 2 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d3]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G ^ 2 + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-3 + 2 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G * G + (3 - 9 * X + 3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-3 + 2 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G * G + (3 - 9 * X + 3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-3 + 2 * X : ℚ⟦X⟧) * G * G * G) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 + 6 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 6 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 18 * X + 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-18 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d6, d9]
    ring
  have hd2 : (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 + 6 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 6 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 18 * X + 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-18 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 : ℚ⟦X⟧) + (-2 + 6 * X : ℚ⟦X⟧) * G + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((-8 * X ^ 2 + 12 * X ^ 3 + 178 * X ^ 4 - 381 * X ^ 5 - 741 * X ^ 6 + 2025 * X ^ 7 - 648 * X ^ 8) * derivative ℚ (derivative ℚ G) + (60 * X ^ 2 - 134 * X ^ 3 - 522 * X ^ 4 + 624 * X ^ 5 + 2268 * X ^ 6 - 1944 * X ^ 7) * derivative ℚ G + (-34 * X ^ 2 + 108 * X ^ 3 + 222 * X ^ 4 - 306 * X ^ 5 - 576 * X ^ 6) * G - (-6 * X ^ 2 + 36 * X ^ 3 + 60 * X ^ 4 - 72 * X ^ 5)) = 0 := by
    linear_combination ((-6 * X ^ 2 + 36 * X ^ 3 + 60 * X ^ 4 - 72 * X ^ 5 : ℚ⟦X⟧) + (-8 * X ^ 2 + 252 * X ^ 3 - 450 * X ^ 4 - 1278 * X ^ 5 + 1872 * X ^ 6 : ℚ⟦X⟧) * G + (-8 * X ^ 2 - 174 * X ^ 3 - 354 * X ^ 4 + 3078 * X ^ 5 + 2412 * X ^ 6 - 11664 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (24 * X ^ 2 - 888 * X ^ 3 + 3800 * X ^ 4 + 816 * X ^ 5 - 20112 * X ^ 6 + 8712 * X ^ 7 + 23328 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (-18 * X ^ 2 + 666 * X ^ 3 - 2868 * X ^ 4 + 14070 * X ^ 6 - 10188 * X ^ 7 - 13374 * X ^ 8 + 5832 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((60 * X ^ 2 - 134 * X ^ 3 - 522 * X ^ 4 + 624 * X ^ 5 + 2268 * X ^ 6 - 1944 * X ^ 7 : ℚ⟦X⟧) + (16 * X ^ 2 - 72 * X ^ 3 - 284 * X ^ 4 + 1830 * X ^ 5 - 804 * X ^ 6 - 8496 * X ^ 7 + 13446 * X ^ 8 - 3888 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (144 * X ^ 2 - 1112 * X ^ 3 + 1656 * X ^ 4 + 4188 * X ^ 5 - 7308 * X ^ 6 - 10692 * X ^ 7 + 15552 * X ^ 8 : ℚ⟦X⟧) * G + (-16 * X ^ 2 - 24 * X ^ 3 + 668 * X ^ 4 - 54 * X ^ 5 - 9108 * X ^ 6 + 11034 * X ^ 7 + 33084 * X ^ 8 - 64638 * X ^ 9 + 19440 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-120 * X ^ 2 + 244 * X ^ 3 + 3144 * X ^ 4 - 9612 * X ^ 5 - 7938 * X ^ 6 + 40122 * X ^ 7 - 5346 * X ^ 8 - 31104 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (-144 * X ^ 2 + 1080 * X ^ 3 + 468 * X ^ 4 - 23490 * X ^ 5 + 59202 * X ^ 6 + 38286 * X ^ 7 - 343170 * X ^ 8 + 474498 * X ^ 9 - 225990 * X ^ 10 + 34992 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-336 * X ^ 2 + 4040 * X ^ 3 - 16536 * X ^ 4 + 19712 * X ^ 5 + 34728 * X ^ 6 - 96054 * X ^ 7 + 31338 * X ^ 8 + 50706 * X ^ 9 - 19440 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (144 * X ^ 2 - 1080 * X ^ 3 - 324 * X ^ 4 + 22842 * X ^ 5 - 61614 * X ^ 6 - 22032 * X ^ 7 + 332730 * X ^ 8 - 544104 * X ^ 9 + 360342 * X ^ 10 - 106434 * X ^ 11 + 11664 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (252 * X ^ 2 - 2958 * X ^ 3 + 12438 * X ^ 4 - 18426 * X ^ 5 - 14634 * X ^ 6 + 74082 * X ^ 7 - 70398 * X ^ 8 + 12708 * X ^ 9 + 6804 * X ^ 10 - 1944 * X ^ 11 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((-8 * X ^ 2 + 12 * X ^ 3 + 178 * X ^ 4 - 381 * X ^ 5 - 741 * X ^ 6 + 2025 * X ^ 7 - 648 * X ^ 8 : ℚ⟦X⟧) + (-32 * X ^ 2 + 144 * X ^ 3 + 568 * X ^ 4 - 3660 * X ^ 5 + 1608 * X ^ 6 + 16992 * X ^ 7 - 26892 * X ^ 8 + 7776 * X ^ 9 : ℚ⟦X⟧) * G + (16 * X ^ 2 + 24 * X ^ 3 - 668 * X ^ 4 + 54 * X ^ 5 + 9108 * X ^ 6 - 11034 * X ^ 7 - 33084 * X ^ 8 + 64638 * X ^ 9 - 19440 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (96 * X ^ 2 - 720 * X ^ 3 - 312 * X ^ 4 + 15660 * X ^ 5 - 39468 * X ^ 6 - 25524 * X ^ 7 + 228780 * X ^ 8 - 316332 * X ^ 9 + 150660 * X ^ 10 - 23328 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (-72 * X ^ 2 + 540 * X ^ 3 + 162 * X ^ 4 - 11421 * X ^ 5 + 30807 * X ^ 6 + 11016 * X ^ 7 - 166365 * X ^ 8 + 272052 * X ^ 9 - 180171 * X ^ 10 + 53217 * X ^ 11 - 5832 * X ^ 12 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hres : ((72 - 324 * X + 387 * X ^ 2 - 81 * X ^ 3 : ℚ⟦X⟧) + (-54 * X + 225 * X ^ 2 - 189 * X ^ 3 - 81 * X ^ 4 : ℚ⟦X⟧) * G + (-72 + 486 * X - 1098 * X ^ 2 + 918 * X ^ 3 - 216 * X ^ 4 : ℚ⟦X⟧) * G ^ 2) * ((-1 : ℚ⟦X⟧) + (-2 + 6 * X : ℚ⟦X⟧) * G + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) = (-36 * X ^ 2 + 243 * X ^ 4 : ℚ⟦X⟧) := by
    linear_combination (-((72 - 324 * X + 351 * X ^ 2 - 81 * X ^ 3 + 243 * X ^ 4 : ℚ⟦X⟧) + (216 - 1458 * X + 3294 * X ^ 2 - 2754 * X ^ 3 + 648 * X ^ 4 : ℚ⟦X⟧) * G)) * hP
  have hd0 : (-36 + 243 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (36 : ℚ⟦X⟧) = 36 := cnum 36
    simp [kc] at h'
  have hdisc : (-36 * X ^ 2 + 243 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-36 * X ^ 2 + 243 * X ^ 4 : ℚ⟦X⟧) = X ^ 2 * (-36 + 243 * X ^ 2 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hd0
  have hPG : (-1 : ℚ⟦X⟧) + (-2 + 6 * X : ℚ⟦X⟧) * G + (3 - 9 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    derivative ℚ (derivative ℚ G) * X * X * C (-8) + derivative ℚ (derivative ℚ G) * X * X * X * C 12 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 178 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-381) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-741) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 2025 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-648) + derivative ℚ G * X * X * C 60 +
      derivative ℚ G * X * X * X * C (-134) + derivative ℚ G * X * X * X * X * C (-522) +
      derivative ℚ G * X * X * X * X * X * C 624 + derivative ℚ G * X * X * X * X * X * X * C 2268 +
      derivative ℚ G * X * X * X * X * X * X * X * C (-1944) + G * X * X * C (-34) +
      G * X * X * X * C 108 + G * X * X * X * X * C 222 +
      G * X * X * X * X * X * C (-306) + G * X * X * X * X * X * X * C (-576) =
      C (-6) * X * X + C 36 * X * X * X +
      C 60 * X * X * X * X + C (-72) * X * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) (m : ℕ) :
    (-8) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 12 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      178 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-381) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-741) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 2025 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-648) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 60 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-134) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-522) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      624 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 2268 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-1944) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-34) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      108 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 222 * coeff (m + 1 + 1 + 1 + 1) G +
      (-306) * coeff (m + 1 + 1 + 1) G + (-576) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (-240) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      2136 * coeff (0 + 1 + 1 + 1 + 1) G + (-2286) * coeff (0 + 1 + 1 + 1) G +
      (-1482) * coeff (0 + 1 + 1) G + 300 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-536) * coeff (0 + 1 + 1 + 1 + 1) G + (-1566) * coeff (0 + 1 + 1 + 1) G +
      1248 * coeff (0 + 1 + 1) G + 2268 * coeff (0 + 1) G +
      (-34) * coeff (0 + 1 + 1 + 1 + 1) G + 108 * coeff (0 + 1 + 1 + 1) G +
      222 * coeff (0 + 1 + 1) G + (-306) * coeff (0 + 1) G +
      (-576) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (-1 + 3 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (-336) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 360 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3560 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-4572) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-4446) * coeff (0 + 1 + 1 + 1) G + 4050 * coeff (0 + 1 + 1) G +
      360 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-670) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-2088) * coeff (0 + 1 + 1 + 1 + 1) G + 1872 * coeff (0 + 1 + 1 + 1) G +
      4536 * coeff (0 + 1 + 1) G + (-1944) * coeff (0 + 1) G +
      (-34) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 108 * coeff (0 + 1 + 1 + 1 + 1) G +
      222 * coeff (0 + 1 + 1 + 1) G + (-306) * coeff (0 + 1 + 1) G +
      (-576) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A138164Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a138164.main := by
  intro T G hT hT0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hT0c : PowerSeries.constantCoeff T = 0 := by simpa using hT0
  have hN1 : ((1) + (-1) * T + (-1) * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hT0c] at h'
  have hM : ((1) + (-1) * T + (-1) * T ^ 2) ^ 3 * ((1 : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (-1 + 3 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3) = 0 := by
    linear_combination ((2) * T + (3) * T ^ 2 + (1) * T ^ 3 + (-1) * PowerSeries.X) * hT +
      ((-1) + (3) * T + (2) * T ^ 2 + (-2) * T ^ 3 + (-1) * T ^ 4 + (1) * G * T + (-2) * G * T ^ 3 + (-1) * G * T ^ 4 + (1) * G ^ 2 + (-2) * G ^ 2 * T + (-1) * G ^ 2 * T ^ 2 + (2) * G ^ 2 * T ^ 3 + (1) * G ^ 2 * T ^ 4 + (-3) * PowerSeries.X * T + (-3) * PowerSeries.X * T ^ 2 + (-3) * PowerSeries.X * G * T + (6) * PowerSeries.X * G * T ^ 3 + (3) * PowerSeries.X * G * T ^ 4 + (-3) * PowerSeries.X * G ^ 2 + (6) * PowerSeries.X * G ^ 2 * T + (3) * PowerSeries.X * G ^ 2 * T ^ 2 + (-6) * PowerSeries.X * G ^ 2 * T ^ 3 + (-3) * PowerSeries.X * G ^ 2 * T ^ 4 + (1) * PowerSeries.X ^ 2 + (1) * PowerSeries.X ^ 2 * G + (-1) * PowerSeries.X ^ 2 * G * T + (-1) * PowerSeries.X ^ 2 * G * T ^ 2 + (1) * PowerSeries.X ^ 2 * G ^ 2 + (-2) * PowerSeries.X ^ 2 * G ^ 2 * T + (-1) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 + (2) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 + (1) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 4) * hG
  have hP : (1 : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (-1 + 3 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 3 hN1)
  cases m with
  | zero =>
    have r := A138164Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A138164Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A138164Aux.rel G hP m
      push_cast
      linear_combination r
