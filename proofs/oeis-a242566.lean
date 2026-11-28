import OMAStatements.S_oeis_a242566

-- Problem: A242566: Expansion of (1-sqrt(1-(2*(1-sqrt(1-4*x^2)))/x))/2.
-- Upstream: formal-conjectures statements/oeis-a242566.lean:0 (declaration OMA.S_oeis_a242566.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A242566Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + X : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (4 * X ^ 2 - 49 * X ^ 3 + 120 * X ^ 4 + 196 * X ^ 5 - 544 * X ^ 6) * derivative ℚ (derivative ℚ G) + (6 * X - 50 * X ^ 2 + 96 * X ^ 3 + 396 * X ^ 4 - 1088 * X ^ 5) * derivative ℚ G + (12 * X - 36 * X ^ 2) * G =
      6 * X - 18 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hp0 : (1 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 1 * X : ℚ⟦X⟧) * G * G + (-2 * X : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 1 * X : ℚ⟦X⟧) * G * G + (-2 * X : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 2 + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 2 + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G + (-6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G + (-6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 + 2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d6]
    ring
  have hd2 : (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 + 2 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 + 2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 : ℚ⟦X⟧) + (2 + 2 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((4 * X ^ 2 - 49 * X ^ 3 + 120 * X ^ 4 + 196 * X ^ 5 - 544 * X ^ 6) * derivative ℚ (derivative ℚ G) + (6 * X - 50 * X ^ 2 + 96 * X ^ 3 + 396 * X ^ 4 - 1088 * X ^ 5) * derivative ℚ G + (12 * X - 36 * X ^ 2) * G - (6 * X - 18 * X ^ 2)) = 0 := by
    linear_combination ((24 * X - 6 * X ^ 2 - 538 * X ^ 3 + 456 * X ^ 4 + 696 * X ^ 5 + 1088 * X ^ 6 : ℚ⟦X⟧) + (-90 * X - 2 * X ^ 2 + 1356 * X ^ 3 - 1416 * X ^ 4 + 1264 * X ^ 5 - 6528 * X ^ 6 : ℚ⟦X⟧) * G + (66 * X + 680 * X ^ 2 - 2938 * X ^ 3 - 576 * X ^ 4 + 1592 * X ^ 5 + 7616 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (48 * X - 1340 * X ^ 2 + 2576 * X ^ 3 + 5424 * X ^ 4 - 3296 * X ^ 5 - 8704 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (-24 * X + 630 * X ^ 2 + 182 * X ^ 3 - 6312 * X ^ 4 - 4392 * X ^ 5 + 20672 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (48 * X ^ 2 - 1764 * X ^ 3 + 4320 * X ^ 4 + 7248 * X ^ 5 - 19584 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (-16 * X ^ 2 + 588 * X ^ 3 - 1440 * X ^ 4 - 2416 * X ^ 5 + 6528 * X ^ 6 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((6 * X - 42 * X ^ 2 + 6 * X ^ 3 + 538 * X ^ 4 - 456 * X ^ 5 - 696 * X ^ 6 - 1088 * X ^ 7 : ℚ⟦X⟧) + (8 * X ^ 2 - 90 * X ^ 3 + 142 * X ^ 4 + 632 * X ^ 5 - 696 * X ^ 6 - 1088 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (-24 * X + 192 * X ^ 2 - 428 * X ^ 3 - 900 * X ^ 4 + 2112 * X ^ 5 - 176 * X ^ 6 + 6528 * X ^ 7 : ℚ⟦X⟧) * G + (-16 * X ^ 2 + 116 * X ^ 3 + 484 * X ^ 4 - 2988 * X ^ 5 - 2224 * X ^ 6 + 10096 * X ^ 7 + 2176 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (24 * X - 152 * X ^ 2 + 314 * X ^ 3 + 850 * X ^ 4 + 1144 * X ^ 5 - 9208 * X ^ 6 - 7616 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (192 * X ^ 3 - 2208 * X ^ 4 + 3996 * X ^ 5 + 13728 * X ^ 6 - 19056 * X ^ 7 - 19584 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-80 * X ^ 2 + 212 * X ^ 3 - 80 * X ^ 4 - 5648 * X ^ 5 + 16352 * X ^ 6 + 8704 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-128 * X ^ 3 + 1152 * X ^ 4 + 1256 * X ^ 5 - 18752 * X ^ 6 - 2976 * X ^ 7 + 56576 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (40 * X ^ 2 - 66 * X ^ 3 + 490 * X ^ 4 + 664 * X ^ 5 - 2136 * X ^ 6 - 20672 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (480 * X ^ 4 - 5880 * X ^ 5 + 14400 * X ^ 6 + 23520 * X ^ 7 - 65280 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-48 * X ^ 3 - 540 * X ^ 4 + 2592 * X ^ 5 - 7248 * X ^ 6 + 19584 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 + (-192 * X ^ 4 + 2352 * X ^ 5 - 5760 * X ^ 6 - 9408 * X ^ 7 + 26112 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (16 * X ^ 3 + 180 * X ^ 4 - 864 * X ^ 5 + 2416 * X ^ 6 - 6528 * X ^ 7 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((4 * X ^ 2 - 49 * X ^ 3 + 120 * X ^ 4 + 196 * X ^ 5 - 544 * X ^ 6 : ℚ⟦X⟧) + (-16 * X ^ 2 + 180 * X ^ 3 - 284 * X ^ 4 - 1264 * X ^ 5 + 1392 * X ^ 6 + 2176 * X ^ 7 : ℚ⟦X⟧) * G + (16 * X ^ 2 - 116 * X ^ 3 - 484 * X ^ 4 + 2988 * X ^ 5 + 2224 * X ^ 6 - 10096 * X ^ 7 - 2176 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (-128 * X ^ 3 + 1472 * X ^ 4 - 2664 * X ^ 5 - 9152 * X ^ 6 + 12704 * X ^ 7 + 13056 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (64 * X ^ 3 - 576 * X ^ 4 - 628 * X ^ 5 + 9376 * X ^ 6 + 1488 * X ^ 7 - 28288 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (-192 * X ^ 4 + 2352 * X ^ 5 - 5760 * X ^ 6 - 9408 * X ^ 7 + 26112 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (64 * X ^ 4 - 784 * X ^ 5 + 1920 * X ^ 6 + 3136 * X ^ 7 - 8704 * X ^ 8 : ℚ⟦X⟧) * G ^ 6) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hPG : (-1 : ℚ⟦X⟧) + (2 + 2 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + X : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C (-49) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 120 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 196 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-544) + derivative ℚ G * X * C 6 +
      derivative ℚ G * X * X * C (-50) + derivative ℚ G * X * X * X * C 96 +
      derivative ℚ G * X * X * X * X * C 396 + derivative ℚ G * X * X * X * X * X * C (-1088) +
      G * X * C 12 + G * X * X * C (-36) =
      C 6 * X + C (-18) * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + X : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-49) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      120 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 196 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-544) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 6 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-50) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 96 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      396 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-1088) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      12 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-36) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + X : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-294) * coeff (0 + 1 + 1 + 1) G +
      240 * coeff (0 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-150) * coeff (0 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1) G +
      396 * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + X : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    80 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-588) * coeff (0 + 1 + 1 + 1 + 1) G +
      720 * coeff (0 + 1 + 1 + 1) G + 392 * coeff (0 + 1 + 1) G +
      30 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-200) * coeff (0 + 1 + 1 + 1 + 1) G +
      288 * coeff (0 + 1 + 1 + 1) G + 792 * coeff (0 + 1 + 1) G +
      (-1088) * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A242566Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a242566.main := by
  intro T U G hT _ hU _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hM : ((16 : PowerSeries ℚ) * PowerSeries.X ^ 1) * ((PowerSeries.X : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (1 + PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-2 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((4)) * hT + ((2) + (2) * T + (-1) * PowerSeries.X + (1) * PowerSeries.X * U ^ 2) * hU + ((-4) * PowerSeries.X + (-4) * PowerSeries.X * U + (8) * PowerSeries.X * G + (1) * PowerSeries.X ^ 2 + (1) * PowerSeries.X ^ 2 * U + (-1) * PowerSeries.X ^ 2 * U ^ 2 + (-1) * PowerSeries.X ^ 2 * U ^ 3 + (2) * PowerSeries.X ^ 2 * G + (4) * PowerSeries.X ^ 2 * G * U + (2) * PowerSeries.X ^ 2 * G * U ^ 2 + (-12) * PowerSeries.X ^ 2 * G ^ 2 + (-4) * PowerSeries.X ^ 2 * G ^ 2 * U + (8) * PowerSeries.X ^ 2 * G ^ 3) * hG
  have hc : (16 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    rw [A242566Aux.cnum, map_zero] at h'
    norm_num at h'
  have hMne : ((16 : PowerSeries ℚ) * PowerSeries.X ^ 1) ≠ 0 := mul_ne_zero hc (pow_ne_zero 1 PowerSeries.X_ne_zero)
  have hP : (PowerSeries.X : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (1 + PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-2 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left hMne
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A242566Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A242566Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A242566Aux.rel G hP h0c m
      push_cast
      linear_combination r
