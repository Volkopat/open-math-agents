import OMAStatements.S_oeis_a182887

-- Problem: A182887: Number of (1,0)-steps in all weighted lattice paths in L_n.
-- Upstream: formal-conjectures statements/oeis-a182887.lean:0 (declaration OMA.S_oeis_a182887.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A182887Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X - 2 * X ^ 3 - X ^ 4 + (0) * S) :
    (2 * X - 4 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + 10 * X ^ 5 + 10 * X ^ 6 - 2 * X ^ 8) * derivative ℚ G + (-2 - 2 * X + 8 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 5 - 10 * X ^ 6 - 4 * X ^ 7) * G = 0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have hS2 : S * S = (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * G = (0 : ℚ⟦X⟧) + (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) * S := by
    linear_combination (0 - (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) * hG + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * ((1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 6 * X - 9 * (X * X) + 2 * (X * X * X) - 18 * (X * X * X * X) + 30 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) + 30 * (X * X * X * X * X * X * X) - 18 * (X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X) - 9 * (X * X * X * X * X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (6 - 18 * X + 6 * X ^ 2 - 72 * X ^ 3 + 150 * X ^ 4 + 42 * X ^ 5 + 210 * X ^ 6 - 144 * X ^ 7 + 18 * X ^ 8 - 90 * X ^ 9 + 66 * X ^ 10 - 12 * X ^ 11) * G + (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d6, d7, d9, d18, d30]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 * X + 2 * (X * X) + 3 * (X * X * X) - 1 * (X * X * X * X) - 5 * (X * X * X * X * X) - 5 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      0 + (-1 + 4 * X + 9 * X ^ 2 - 4 * X ^ 3 - 25 * X ^ 4 - 30 * X ^ 5 + 8 * X ^ 7) * S + (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d3, d5]
    ring
  have hk2 : (-1 + 6 * X - 9 * (X * X) + 2 * (X * X * X) - 18 * (X * X * X * X) + 30 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) + 30 * (X * X * X * X * X * X * X) - 18 * (X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X) - 9 * (X * X * X * X * X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 * X + 2 * (X * X) + 3 * (X * X * X) - 1 * (X * X * X * X) - 5 * (X * X * X * X * X) - 5 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (6 - 18 * X + 6 * X ^ 2 - 72 * X ^ 3 + 150 * X ^ 4 + 42 * X ^ 5 + 210 * X ^ 6 - 144 * X ^ 7 + 18 * X ^ 8 - 90 * X ^ 9 + 66 * X ^ 10 - 12 * X ^ 11) * G + (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * derivative ℚ G =
      0 + (-1 + 4 * X + 9 * X ^ 2 - 4 * X ^ 3 - 25 * X ^ 4 - 30 * X ^ 5 + 8 * X ^ 7) * S + (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 8 * X + 20 * X ^ 2 - 16 * X ^ 3 + 26 * X ^ 4 - 88 * X ^ 5 + 48 * X ^ 6 - 24 * X ^ 7 + 163 * X ^ 8 - 24 * X ^ 9 + 48 * X ^ 10 - 88 * X ^ 11 + 26 * X ^ 12 - 16 * X ^ 13 + 20 * X ^ 14 - 8 * X ^ 15 + X ^ 16) * ((2 * X - 4 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + 10 * X ^ 5 + 10 * X ^ 6 - 2 * X ^ 8) * derivative ℚ G + (-2 - 2 * X + 8 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 5 - 10 * X ^ 6 - 4 * X ^ 7) * G - (0)) = 0 := by
    linear_combination (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) ^ 2 * S * hdS - 2 * (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) ^ 2 * derivative ℚ S * hS -
      (2 * (-1 + 4 * X + 9 * X ^ 2 - 4 * X ^ 3 - 25 * X ^ 4 - 30 * X ^ 5 + 8 * X ^ 7) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) + (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-X + 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 - 5 * X ^ 5 - 5 * X ^ 6 + X ^ 8) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * hdk
  have hg : (1 - 8 * X + 20 * X ^ 2 - 16 * X ^ 3 + 26 * X ^ 4 - 88 * X ^ 5 + 48 * X ^ 6 - 24 * X ^ 7 + 163 * X ^ 8 - 24 * X ^ 9 + 48 * X ^ 10 - 88 * X ^ 11 + 26 * X ^ 12 - 16 * X ^ 13 + 20 * X ^ 14 - 8 * X ^ 15 + X ^ 16 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X - 2 * X ^ 3 - X ^ 4 + (0) * S) :
    (182 * X ^ 2 - 230 * X ^ 3 - 450 * X ^ 4 - 498 * X ^ 5 - 86 * X ^ 6 + 134 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-279 * X - 679 * X ^ 2 - 647 * X ^ 3 - 2515 * X ^ 4 + 185 * X ^ 5 + 1013 * X ^ 6) * derivative ℚ G + (279 + 424 * X + 1091 * X ^ 2 - 1512 * X ^ 3 + 1931 * X ^ 4 + 1222 * X ^ 5) * G =
      0 := by
  have h := key S G hS hG
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have hL : derivative ℚ ((2 * X - 4 * (X * X) - 6 * (X * X * X) + 2 * (X * X * X * X) + 10 * (X * X * X * X * X) + 10 * (X * X * X * X * X * X) - 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 - 2 * X + 8 * (X * X) - 18 * (X * X * X) + 10 * (X * X * X * X * X) - 10 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (2 - 8 * X - 18 * X ^ 2 + 8 * X ^ 3 + 50 * X ^ 4 + 60 * X ^ 5 - 16 * X ^ 7) * derivative ℚ G + (2 * X - 4 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + 10 * X ^ 5 + 10 * X ^ 6 - 2 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-2 + 16 * X - 54 * X ^ 2 + 50 * X ^ 4 - 60 * X ^ 5 - 28 * X ^ 6) * G + (-2 - 2 * X + 8 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 5 - 10 * X ^ 6 - 4 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d10, d18]
    ring
  have hRd : derivative ℚ (0 : ℚ⟦X⟧) = 0 := by
    simp
  have h2 : (2 * X - 4 * (X * X) - 6 * (X * X * X) + 2 * (X * X * X * X) + 10 * (X * X * X * X * X) + 10 * (X * X * X * X * X * X) - 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 - 2 * X + 8 * (X * X) - 18 * (X * X * X) + 10 * (X * X * X * X * X) - 10 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) := by linear_combination h
  have hd : (2 - 8 * X - 18 * X ^ 2 + 8 * X ^ 3 + 50 * X ^ 4 + 60 * X ^ 5 - 16 * X ^ 7) * derivative ℚ G + (2 * X - 4 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + 10 * X ^ 5 + 10 * X ^ 6 - 2 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-2 + 16 * X - 54 * X ^ 2 + 50 * X ^ 4 - 60 * X ^ 5 - 28 * X ^ 6) * G + (-2 - 2 * X + 8 * X ^ 2 - 18 * X ^ 3 + 10 * X ^ 5 - 10 * X ^ 6 - 4 * X ^ 7) * derivative ℚ G = 0 := by
    rw [← hL, h2, hRd]
  have hfull : (2 - 4 * X ^ 2 - 2 * X ^ 3) * ((182 * X ^ 2 - 230 * X ^ 3 - 450 * X ^ 4 - 498 * X ^ 5 - 86 * X ^ 6 + 134 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-279 * X - 679 * X ^ 2 - 647 * X ^ 3 - 2515 * X ^ 4 + 185 * X ^ 5 + 1013 * X ^ 6) * derivative ℚ G + (279 + 424 * X + 1091 * X ^ 2 - 1512 * X ^ 3 + 1931 * X ^ 4 + 1222 * X ^ 5) * G - (0)) = 0 := by
    linear_combination (182 * X + 134 * X ^ 2) * hd + (-279 - 327 * X) * h
  have hg : (2 - 4 * X ^ 2 - 2 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X - 2 * X ^ 3 - X ^ 4 + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 182 + derivative ℚ (derivative ℚ G) * X * X * X * C (-230) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-450) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-498) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-86) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 134 +
      derivative ℚ G * X * C (-279) + derivative ℚ G * X * X * C (-679) +
      derivative ℚ G * X * X * X * C (-647) + derivative ℚ G * X * X * X * X * C (-2515) +
      derivative ℚ G * X * X * X * X * X * C 185 + derivative ℚ G * X * X * X * X * X * X * C 1013 +
      G * C 279 + G * X * C 424 +
      G * X * X * C 1091 + G * X * X * X * C (-1512) +
      G * X * X * X * X * C 1931 + G * X * X * X * X * X * C 1222 =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X - 2 * X ^ 3 - X ^ 4 + (0) * S) (m : ℕ) :
    182 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-230) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-450) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-498) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-86) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 134 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-279) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-679) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-647) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2515) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      185 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 1013 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      279 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 424 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      1091 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1512) * coeff (m + 1 + 1 + 1 + 1) G +
      1931 * coeff (m + 1 + 1 + 1) G + 1222 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X - 2 * X ^ 3 - X ^ 4 + (0) * S) :
    3640 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-2760) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2700) * coeff (0 + 1 + 1 + 1) G + (-996) * coeff (0 + 1 + 1) G +
      (-1395) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-2716) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1941) * coeff (0 + 1 + 1 + 1) G + (-5030) * coeff (0 + 1 + 1) G +
      185 * coeff (0 + 1) G + 279 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      424 * coeff (0 + 1 + 1 + 1 + 1) G + 1091 * coeff (0 + 1 + 1 + 1) G +
      (-1512) * coeff (0 + 1 + 1) G + 1931 * coeff (0 + 1) G +
      1222 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X - 2 * X ^ 3 - X ^ 4 + (0) * S) :
    5460 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4600) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-5400) * coeff (0 + 1 + 1 + 1 + 1) G + (-2988) * coeff (0 + 1 + 1 + 1) G +
      (-172) * coeff (0 + 1 + 1) G + (-1674) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3395) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-2588) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-7545) * coeff (0 + 1 + 1 + 1) G + 370 * coeff (0 + 1 + 1) G +
      1013 * coeff (0 + 1) G + 279 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      424 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1091 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1512) * coeff (0 + 1 + 1 + 1) G + 1931 * coeff (0 + 1 + 1) G +
      1222 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A182887Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182887.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  cases m with
  | zero =>
    have r := A182887Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A182887Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A182887Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
