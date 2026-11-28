import OMAStatements.S_oeis_a143017

-- Problem: A143017: Number of {2-1-3, 2'^e-31}-avoiding permutations of size n (see definition in the Elizalde paper).
-- Upstream: formal-conjectures statements/oeis-a143017.lean:0 (declaration OMA.S_oeis_a143017.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A143017Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (X : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-8 * X ^ 2 + 8 * X ^ 3 + 4 * X ^ 4 + 140 * X ^ 5 + 50 * X ^ 6 + 196 * X ^ 7 - 45 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-16 * X + 44 * X ^ 2 + 48 * X ^ 3 + 190 * X ^ 4 + 164 * X ^ 5 + 264 * X ^ 6 - 90 * X ^ 7) * derivative ℚ G + (28 * X + 72 * X ^ 2 + 18 * X ^ 3 + 100 * X ^ 4) * G =
      -16 * X - 24 * X ^ 2 - 48 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hp0 : (1 * X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G * G + (1 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G * G + (1 * X : ℚ⟦X⟧) * G * G * G) =
      (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 2 + (3 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 2 + (3 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (3 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (3 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G) =
      (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-4 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d3, d4, d8]
    ring
  have hd2 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-4 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 + 4 * X : ℚ⟦X⟧) + (-4 + 8 * X : ℚ⟦X⟧) * G + (3 * X : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((-8 * X ^ 2 + 8 * X ^ 3 + 4 * X ^ 4 + 140 * X ^ 5 + 50 * X ^ 6 + 196 * X ^ 7 - 45 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-16 * X + 44 * X ^ 2 + 48 * X ^ 3 + 190 * X ^ 4 + 164 * X ^ 5 + 264 * X ^ 6 - 90 * X ^ 7) * derivative ℚ G + (28 * X + 72 * X ^ 2 + 18 * X ^ 3 + 100 * X ^ 4) * G - (-16 * X - 24 * X ^ 2 - 48 * X ^ 4)) = 0 := by
    linear_combination ((28 * X - 144 * X ^ 2 - 510 * X ^ 3 + 2236 * X ^ 4 - 1136 * X ^ 5 + 3066 * X ^ 6 - 60 * X ^ 7 + 360 * X ^ 8 : ℚ⟦X⟧) + (216 * X - 576 * X ^ 2 - 3696 * X ^ 3 + 10952 * X ^ 4 - 5198 * X ^ 5 + 13608 * X ^ 6 - 1776 * X ^ 7 + 1710 * X ^ 8 : ℚ⟦X⟧) * G + (384 * X - 468 * X ^ 2 - 6072 * X ^ 3 + 15598 * X ^ 4 - 8240 * X ^ 5 + 18960 * X ^ 6 - 2592 * X ^ 7 + 2520 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (-128 * X - 960 * X ^ 2 - 1728 * X ^ 3 + 7104 * X ^ 4 - 2432 * X ^ 5 + 9792 * X ^ 6 - 848 * X ^ 7 + 1440 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (48 * X ^ 2 + 456 * X ^ 3 + 1560 * X ^ 4 + 456 * X ^ 5 + 1824 * X ^ 6 - 24 * X ^ 7 + 270 * X ^ 8 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-16 * X + 140 * X ^ 2 - 336 * X ^ 3 + 334 * X ^ 4 - 124 * X ^ 5 - 1168 * X ^ 6 + 6 * X ^ 7 + 60 * X ^ 8 - 360 * X ^ 9 : ℚ⟦X⟧) + (32 * X ^ 2 - 224 * X ^ 3 + 432 * X ^ 4 - 720 * X ^ 5 + 3032 * X ^ 6 - 4064 * X ^ 7 + 3284 * X ^ 8 - 7352 * X ^ 9 + 1440 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) + (-128 * X + 864 * X ^ 2 - 1776 * X ^ 3 + 1440 * X ^ 4 - 616 * X ^ 5 - 4600 * X ^ 6 - 1124 * X ^ 7 + 2136 * X ^ 8 - 1710 * X ^ 9 : ℚ⟦X⟧) * G + (128 * X ^ 2 - 688 * X ^ 3 + 1200 * X ^ 4 - 2664 * X ^ 5 + 8648 * X ^ 6 - 11956 * X ^ 7 + 10040 * X ^ 8 - 20398 * X ^ 9 + 3960 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-256 * X + 1392 * X ^ 2 - 2328 * X ^ 3 + 2808 * X ^ 4 + 628 * X ^ 5 - 4636 * X ^ 6 - 904 * X ^ 7 + 3582 * X ^ 8 - 2520 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (-288 * X ^ 3 + 864 * X ^ 4 - 432 * X ^ 5 + 4752 * X ^ 6 - 8280 * X ^ 7 + 3456 * X ^ 8 - 15732 * X ^ 9 + 3240 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (224 * X ^ 2 - 1152 * X ^ 3 + 528 * X ^ 4 + 288 * X ^ 5 - 2776 * X ^ 6 + 2256 * X ^ 7 + 1388 * X ^ 8 - 1440 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (144 * X ^ 4 - 144 * X ^ 5 - 72 * X ^ 6 - 2520 * X ^ 7 - 900 * X ^ 8 - 3528 * X ^ 9 + 810 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-48 * X ^ 3 + 300 * X ^ 4 + 384 * X ^ 5 + 30 * X ^ 6 + 876 * X ^ 7 + 24 * X ^ 8 - 270 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((-8 * X ^ 2 + 72 * X ^ 3 - 188 * X ^ 4 + 236 * X ^ 5 - 1006 * X ^ 6 + 2036 * X ^ 7 - 813 * X ^ 8 + 3496 * X ^ 9 - 720 * X ^ 10 : ℚ⟦X⟧) + (-64 * X ^ 2 + 448 * X ^ 3 - 864 * X ^ 4 + 1440 * X ^ 5 - 6064 * X ^ 6 + 8128 * X ^ 7 - 6568 * X ^ 8 + 14704 * X ^ 9 - 2880 * X ^ 10 : ℚ⟦X⟧) * G + (-128 * X ^ 2 + 688 * X ^ 3 - 1200 * X ^ 4 + 2664 * X ^ 5 - 8648 * X ^ 6 + 11956 * X ^ 7 - 10040 * X ^ 8 + 20398 * X ^ 9 - 3960 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (192 * X ^ 3 - 576 * X ^ 4 + 288 * X ^ 5 - 3168 * X ^ 6 + 5520 * X ^ 7 - 2304 * X ^ 8 + 10488 * X ^ 9 - 2160 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-72 * X ^ 4 + 72 * X ^ 5 + 36 * X ^ 6 + 1260 * X ^ 7 + 450 * X ^ 8 + 1764 * X ^ 9 - 405 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hd2
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (-1 + 4 * X : ℚ⟦X⟧) + (-4 + 8 * X : ℚ⟦X⟧) * G + (3 * X : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k4] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (X : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C (-8) + derivative ℚ (derivative ℚ G) * X * X * X * C 8 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 140 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 50 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 196 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-45) + derivative ℚ G * X * C (-16) +
      derivative ℚ G * X * X * C 44 + derivative ℚ G * X * X * X * C 48 +
      derivative ℚ G * X * X * X * X * C 190 + derivative ℚ G * X * X * X * X * X * C 164 +
      derivative ℚ G * X * X * X * X * X * X * C 264 + derivative ℚ G * X * X * X * X * X * X * X * C (-90) +
      G * X * C 28 + G * X * X * C 72 +
      G * X * X * X * C 18 + G * X * X * X * X * C 100 =
      C (-16) * X + C (-24) * X * X +
      C (-48) * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (X : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    (-8) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 8 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 140 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      50 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 196 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-45) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-16) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      44 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 48 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      190 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 164 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      264 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-90) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      28 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 72 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      18 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 100 * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (X : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-240) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 160 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1 + 1 + 1) G + 840 * coeff (0 + 1 + 1 + 1) G +
      100 * coeff (0 + 1 + 1) G + (-96) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      220 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1 + 1 + 1) G +
      570 * coeff (0 + 1 + 1 + 1) G + 328 * coeff (0 + 1 + 1) G +
      264 * coeff (0 + 1) G + 28 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      72 * coeff (0 + 1 + 1 + 1 + 1) G + 18 * coeff (0 + 1 + 1 + 1) G +
      100 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (X : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-336) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 240 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      80 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1680 * coeff (0 + 1 + 1 + 1 + 1) G +
      300 * coeff (0 + 1 + 1 + 1) G + 392 * coeff (0 + 1 + 1) G +
      (-112) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 264 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 760 * coeff (0 + 1 + 1 + 1 + 1) G +
      492 * coeff (0 + 1 + 1 + 1) G + 528 * coeff (0 + 1 + 1) G +
      (-90) * coeff (0 + 1) G + 28 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      72 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 18 * coeff (0 + 1 + 1 + 1 + 1) G +
      100 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A143017Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a143017.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hP : (PowerSeries.X : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G + (-2 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A143017Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A143017Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A143017Aux.rel G hP h0c m
      push_cast
      linear_combination r
