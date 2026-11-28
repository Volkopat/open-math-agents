import OMAStatements.S_oeis_a182879

-- Problem: A182879: The sum of the lengths of all weighted lattice paths in L_n.
-- Upstream: formal-conjectures statements/oeis-a182879.lean:0 (declaration OMA.S_oeis_a182879.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A182879Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X + 2 * X ^ 3 - X ^ 4 + (0) * S) :
    (2 * X - 4 * X ^ 2 + 2 * X ^ 3 - 14 * X ^ 4 + 2 * X ^ 5 - 6 * X ^ 6 + 8 * X ^ 7 - 2 * X ^ 8) * derivative ℚ G + (-2 - 2 * X - 16 * X ^ 2 + 6 * X ^ 3 - 14 * X ^ 5 + 14 * X ^ 6 - 4 * X ^ 7) * G = 0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have hS2 : S * S = (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * G = (0 : ℚ⟦X⟧) + (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) * S := by
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
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 * X + 2 * (X * X) - 1 * (X * X * X) + 7 * (X * X * X * X) - 1 * (X * X * X * X * X) + 3 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      0 + (-1 + 4 * X - 3 * X ^ 2 + 28 * X ^ 3 - 5 * X ^ 4 + 18 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7) * S + (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d3, d4, d7]
    ring
  have hk2 : (-1 + 6 * X - 9 * (X * X) + 2 * (X * X * X) - 18 * (X * X * X * X) + 30 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) + 30 * (X * X * X * X * X * X * X) - 18 * (X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X) - 9 * (X * X * X * X * X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 * X + 2 * (X * X) - 1 * (X * X * X) + 7 * (X * X * X * X) - 1 * (X * X * X * X * X) + 3 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (6 - 18 * X + 6 * X ^ 2 - 72 * X ^ 3 + 150 * X ^ 4 + 42 * X ^ 5 + 210 * X ^ 6 - 144 * X ^ 7 + 18 * X ^ 8 - 90 * X ^ 9 + 66 * X ^ 10 - 12 * X ^ 11) * G + (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * derivative ℚ G =
      0 + (-1 + 4 * X - 3 * X ^ 2 + 28 * X ^ 3 - 5 * X ^ 4 + 18 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7) * S + (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 8 * X + 20 * X ^ 2 - 16 * X ^ 3 + 26 * X ^ 4 - 88 * X ^ 5 + 48 * X ^ 6 - 24 * X ^ 7 + 163 * X ^ 8 - 24 * X ^ 9 + 48 * X ^ 10 - 88 * X ^ 11 + 26 * X ^ 12 - 16 * X ^ 13 + 20 * X ^ 14 - 8 * X ^ 15 + X ^ 16) * ((2 * X - 4 * X ^ 2 + 2 * X ^ 3 - 14 * X ^ 4 + 2 * X ^ 5 - 6 * X ^ 6 + 8 * X ^ 7 - 2 * X ^ 8) * derivative ℚ G + (-2 - 2 * X - 16 * X ^ 2 + 6 * X ^ 3 - 14 * X ^ 5 + 14 * X ^ 6 - 4 * X ^ 7) * G - (0)) = 0 := by
    linear_combination (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) ^ 2 * S * hdS - 2 * (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) ^ 2 * derivative ℚ S * hS -
      (2 * (-1 + 4 * X - 3 * X ^ 2 + 28 * X ^ 3 - 5 * X ^ 4 + 18 * X ^ 5 - 28 * X ^ 6 + 8 * X ^ 7) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) + (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-X + 2 * X ^ 2 - X ^ 3 + 7 * X ^ 4 - X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 + X ^ 8) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * hdk
  have hg : (1 - 8 * X + 20 * X ^ 2 - 16 * X ^ 3 + 26 * X ^ 4 - 88 * X ^ 5 + 48 * X ^ 6 - 24 * X ^ 7 + 163 * X ^ 8 - 24 * X ^ 9 + 48 * X ^ 10 - 88 * X ^ 11 + 26 * X ^ 12 - 16 * X ^ 13 + 20 * X ^ 14 - 8 * X ^ 15 + X ^ 16 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X + 2 * X ^ 3 - X ^ 4 + (0) * S) :
    (310 * X ^ 2 - 882 * X ^ 3 + 214 * X ^ 4 - 358 * X ^ 5 + 834 * X ^ 6 - 262 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-781 * X + 1199 * X ^ 2 - 1833 * X ^ 3 - 2965 * X ^ 4 + 3875 * X ^ 5 - 1433 * X ^ 6) * derivative ℚ G + (781 - 716 * X - 1199 * X ^ 2 - 2644 * X ^ 3 + 2885 * X ^ 4 - 1294 * X ^ 5) * G =
      0 := by
  have h := key S G hS hG
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hL : derivative ℚ ((2 * X - 4 * (X * X) + 2 * (X * X * X) - 14 * (X * X * X * X) + 2 * (X * X * X * X * X) - 6 * (X * X * X * X * X * X) + 8 * (X * X * X * X * X * X * X) - 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 - 2 * X - 16 * (X * X) + 6 * (X * X * X) - 14 * (X * X * X * X * X) + 14 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (2 - 8 * X + 6 * X ^ 2 - 56 * X ^ 3 + 10 * X ^ 4 - 36 * X ^ 5 + 56 * X ^ 6 - 16 * X ^ 7) * derivative ℚ G + (2 * X - 4 * X ^ 2 + 2 * X ^ 3 - 14 * X ^ 4 + 2 * X ^ 5 - 6 * X ^ 6 + 8 * X ^ 7 - 2 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-2 - 32 * X + 18 * X ^ 2 - 70 * X ^ 4 + 84 * X ^ 5 - 28 * X ^ 6) * G + (-2 - 2 * X - 16 * X ^ 2 + 6 * X ^ 3 - 14 * X ^ 5 + 14 * X ^ 6 - 4 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d14, d16]
    ring
  have hRd : derivative ℚ (0 : ℚ⟦X⟧) = 0 := by
    simp
  have h2 : (2 * X - 4 * (X * X) + 2 * (X * X * X) - 14 * (X * X * X * X) + 2 * (X * X * X * X * X) - 6 * (X * X * X * X * X * X) + 8 * (X * X * X * X * X * X * X) - 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 - 2 * X - 16 * (X * X) + 6 * (X * X * X) - 14 * (X * X * X * X * X) + 14 * (X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) := by linear_combination h
  have hd : (2 - 8 * X + 6 * X ^ 2 - 56 * X ^ 3 + 10 * X ^ 4 - 36 * X ^ 5 + 56 * X ^ 6 - 16 * X ^ 7) * derivative ℚ G + (2 * X - 4 * X ^ 2 + 2 * X ^ 3 - 14 * X ^ 4 + 2 * X ^ 5 - 6 * X ^ 6 + 8 * X ^ 7 - 2 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-2 - 32 * X + 18 * X ^ 2 - 70 * X ^ 4 + 84 * X ^ 5 - 28 * X ^ 6) * G + (-2 - 2 * X - 16 * X ^ 2 + 6 * X ^ 3 - 14 * X ^ 5 + 14 * X ^ 6 - 4 * X ^ 7) * derivative ℚ G = 0 := by
    rw [← hL, h2, hRd]
  have hfull : (2 + 4 * X ^ 2 - 2 * X ^ 3) * ((310 * X ^ 2 - 882 * X ^ 3 + 214 * X ^ 4 - 358 * X ^ 5 + 834 * X ^ 6 - 262 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-781 * X + 1199 * X ^ 2 - 1833 * X ^ 3 - 2965 * X ^ 4 + 3875 * X ^ 5 - 1433 * X ^ 6) * derivative ℚ G + (781 - 716 * X - 1199 * X ^ 2 - 2644 * X ^ 3 + 2885 * X ^ 4 - 1294 * X ^ 5) * G - (0)) = 0 := by
    linear_combination (310 * X - 262 * X ^ 2) * hd + (-781 + 1187 * X) * h
  have hg : (2 + 4 * X ^ 2 - 2 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X + 2 * X ^ 3 - X ^ 4 + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 310 + derivative ℚ (derivative ℚ G) * X * X * X * C (-882) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 214 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-358) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 834 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-262) +
      derivative ℚ G * X * C (-781) + derivative ℚ G * X * X * C 1199 +
      derivative ℚ G * X * X * X * C (-1833) + derivative ℚ G * X * X * X * X * C (-2965) +
      derivative ℚ G * X * X * X * X * X * C 3875 + derivative ℚ G * X * X * X * X * X * X * C (-1433) +
      G * C 781 + G * X * C (-716) +
      G * X * X * C (-1199) + G * X * X * X * C (-2644) +
      G * X * X * X * X * C 2885 + G * X * X * X * X * X * C (-1294) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X + 2 * X ^ 3 - X ^ 4 + (0) * S) (m : ℕ) :
    310 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-882) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      214 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-358) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      834 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-262) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-781) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1199 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1833) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2965) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      3875 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-1433) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      781 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-716) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1199) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2644) * coeff (m + 1 + 1 + 1 + 1) G +
      2885 * coeff (m + 1 + 1 + 1) G + (-1294) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X + 2 * X ^ 3 - X ^ 4 + (0) * S) :
    6200 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-10584) * coeff (0 + 1 + 1 + 1 + 1) G +
      1284 * coeff (0 + 1 + 1 + 1) G + (-716) * coeff (0 + 1 + 1) G +
      (-3905) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 4796 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-5499) * coeff (0 + 1 + 1 + 1) G + (-5930) * coeff (0 + 1 + 1) G +
      3875 * coeff (0 + 1) G + 781 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-716) * coeff (0 + 1 + 1 + 1 + 1) G + (-1199) * coeff (0 + 1 + 1 + 1) G +
      (-2644) * coeff (0 + 1 + 1) G + 2885 * coeff (0 + 1) G +
      (-1294) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = X + 2 * X ^ 3 - X ^ 4 + (0) * S) :
    9300 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-17640) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      2568 * coeff (0 + 1 + 1 + 1 + 1) G + (-2148) * coeff (0 + 1 + 1 + 1) G +
      1668 * coeff (0 + 1 + 1) G + (-4686) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      5995 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-7332) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-8895) * coeff (0 + 1 + 1 + 1) G + 7750 * coeff (0 + 1 + 1) G +
      (-1433) * coeff (0 + 1) G + 781 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-716) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1199) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2644) * coeff (0 + 1 + 1 + 1) G + 2885 * coeff (0 + 1 + 1) G +
      (-1294) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A182879Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182879.main := by
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
    have r := A182879Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A182879Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A182879Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
