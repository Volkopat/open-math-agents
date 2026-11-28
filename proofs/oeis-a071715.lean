import OMAStatements.S_oeis_a071715

-- Problem: A071715: Expansion of (1+x*C^4)*C^4, where C = (1-(1-4*x)^(1/2))/(2*x) is g.f. for Catalan numbers, A000108.
-- Upstream: formal-conjectures statements/oeis-a071715.lean:0 (declaration OMA.S_oeis_a071715.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A071715Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (256 * X ^ 8 + (0) * S) = 128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S) :
    (-65536 * X + 655360 * X ^ 2 - 2228224 * X ^ 3 + 2818048 * X ^ 4 - 655360 * X ^ 5 - 524288 * X ^ 6) * derivative ℚ G + (-458752 + 4063232 * X - 11927552 * X ^ 2 + 12582912 * X ^ 3 - 2359296 * X ^ 4 - 1310720 * X ^ 5) * G = -458752 + 1441792 * X - 1310720 * X ^ 2 - 262144 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1280 : derivative ℚ (1280 : ℚ⟦X⟧) = 0 := dnum 1280
  have d1920 : derivative ℚ (1920 : ℚ⟦X⟧) = 0 := dnum 1920
  have d2560 : derivative ℚ (2560 : ℚ⟦X⟧) = 0 := dnum 2560
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (256 * X ^ 8) * G = (128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 : ℚ⟦X⟧) + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (2048 * X ^ 7) * G + (256 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d256]
    ring
  have hR : derivative ℚ ((128 * X - 1024 * (X * X) + 2560 * (X * X * X) - 1920 * (X * X * X * X) - 256 * (X * X * X * X * X) + 256 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-128 * X + 768 * (X * X) - 1280 * (X * X * X) + 384 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      128 - 2048 * X + 7680 * X ^ 2 - 7680 * X ^ 3 - 1280 * X ^ 4 + 1536 * X ^ 5 + (-128 + 1536 * X - 3840 * X ^ 2 + 1536 * X ^ 3 + 1280 * X ^ 4) * S + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d128, d256, d384, d768, d1024, d1280, d1920, d2560]
    ring
  have hk2 : (256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (128 * X - 1024 * (X * X) + 2560 * (X * X * X) - 1920 * (X * X * X * X) - 256 * (X * X * X * X * X) + 256 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-128 * X + 768 * (X * X) - 1280 * (X * X * X) + 384 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2048 * X ^ 7) * G + (256 * X ^ 8) * derivative ℚ G =
      128 - 2048 * X + 7680 * X ^ 2 - 7680 * X ^ 3 - 1280 * X ^ 4 + 1536 * X ^ 5 + (-128 + 1536 * X - 3840 * X ^ 2 + 1536 * X ^ 3 + 1280 * X ^ 4) * S + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 8 * ((-65536 * X + 655360 * X ^ 2 - 2228224 * X ^ 3 + 2818048 * X ^ 4 - 655360 * X ^ 5 - 524288 * X ^ 6) * derivative ℚ G + (-458752 + 4063232 * X - 11927552 * X ^ 2 + 12582912 * X ^ 3 - 2359296 * X ^ 4 - 1310720 * X ^ 5) * G - (-458752 + 1441792 * X - 1310720 * X ^ 2 - 262144 * X ^ 3)) = 0 := by
    linear_combination (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) ^ 2 * S * hdS - 2 * (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-128 + 1536 * X - 3840 * X ^ 2 + 1536 * X ^ 3 + 1280 * X ^ 4) * (1 - 4 * X) + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * (-4)) * hk + 2 * (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 8 ≠ 0 := pow_ne_zero 8 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (256 * X ^ 8 + (0) * S) = 128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S) :
    (891 * X ^ 2 + 891 * X ^ 3 - 20160 * X ^ 4 + 9360 * X ^ 5) * derivative ℚ (derivative ℚ G) + (13952 * X - 35780 * X ^ 2 - 117884 * X ^ 3 + 91616 * X ^ 4) * derivative ℚ G + (47768 - 288532 * X - 82428 * X ^ 2 + 147140 * X ^ 3) * G =
      47768 + 20068 * X := by
  have h := key S G hS hG
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d262144 : derivative ℚ (262144 : ℚ⟦X⟧) = 0 := dnum 262144
  have d458752 : derivative ℚ (458752 : ℚ⟦X⟧) = 0 := dnum 458752
  have d524288 : derivative ℚ (524288 : ℚ⟦X⟧) = 0 := dnum 524288
  have d655360 : derivative ℚ (655360 : ℚ⟦X⟧) = 0 := dnum 655360
  have d1310720 : derivative ℚ (1310720 : ℚ⟦X⟧) = 0 := dnum 1310720
  have d1441792 : derivative ℚ (1441792 : ℚ⟦X⟧) = 0 := dnum 1441792
  have d2228224 : derivative ℚ (2228224 : ℚ⟦X⟧) = 0 := dnum 2228224
  have d2359296 : derivative ℚ (2359296 : ℚ⟦X⟧) = 0 := dnum 2359296
  have d2818048 : derivative ℚ (2818048 : ℚ⟦X⟧) = 0 := dnum 2818048
  have d4063232 : derivative ℚ (4063232 : ℚ⟦X⟧) = 0 := dnum 4063232
  have d11927552 : derivative ℚ (11927552 : ℚ⟦X⟧) = 0 := dnum 11927552
  have d12582912 : derivative ℚ (12582912 : ℚ⟦X⟧) = 0 := dnum 12582912
  have hL : derivative ℚ ((-65536 * X + 655360 * (X * X) - 2228224 * (X * X * X) + 2818048 * (X * X * X * X) - 655360 * (X * X * X * X * X) - 524288 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-458752 + 4063232 * X - 11927552 * (X * X) + 12582912 * (X * X * X) - 2359296 * (X * X * X * X) - 1310720 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (-65536 + 1310720 * X - 6684672 * X ^ 2 + 11272192 * X ^ 3 - 3276800 * X ^ 4 - 3145728 * X ^ 5) * derivative ℚ G + (-65536 * X + 655360 * X ^ 2 - 2228224 * X ^ 3 + 2818048 * X ^ 4 - 655360 * X ^ 5 - 524288 * X ^ 6) * derivative ℚ (derivative ℚ G) + (4063232 - 23855104 * X + 37748736 * X ^ 2 - 9437184 * X ^ 3 - 6553600 * X ^ 4) * G + (-458752 + 4063232 * X - 11927552 * X ^ 2 + 12582912 * X ^ 3 - 2359296 * X ^ 4 - 1310720 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d65536, d458752, d524288, d655360, d1310720, d2228224, d2359296, d2818048, d4063232, d11927552, d12582912]
    ring
  have hRd : derivative ℚ (-458752 + 1441792 * X - 1310720 * (X * X) - 262144 * (X * X * X) : ℚ⟦X⟧) = 1441792 - 2621440 * X - 786432 * X ^ 2 := by
    simp [Derivation.leibniz, d262144, d458752, d1310720, d1441792]
    ring
  have h2 : (-65536 * X + 655360 * (X * X) - 2228224 * (X * X * X) + 2818048 * (X * X * X * X) - 655360 * (X * X * X * X * X) - 524288 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-458752 + 4063232 * X - 11927552 * (X * X) + 12582912 * (X * X * X) - 2359296 * (X * X * X * X) - 1310720 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (-458752 + 1441792 * X - 1310720 * (X * X) - 262144 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-65536 + 1310720 * X - 6684672 * X ^ 2 + 11272192 * X ^ 3 - 3276800 * X ^ 4 - 3145728 * X ^ 5) * derivative ℚ G + (-65536 * X + 655360 * X ^ 2 - 2228224 * X ^ 3 + 2818048 * X ^ 4 - 655360 * X ^ 5 - 524288 * X ^ 6) * derivative ℚ (derivative ℚ G) + (4063232 - 23855104 * X + 37748736 * X ^ 2 - 9437184 * X ^ 3 - 6553600 * X ^ 4) * G + (-458752 + 4063232 * X - 11927552 * X ^ 2 + 12582912 * X ^ 3 - 2359296 * X ^ 4 - 1310720 * X ^ 5) * derivative ℚ G = 1441792 - 2621440 * X - 786432 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hfull : (65536 - 393216 * X + 655360 * X ^ 2 - 196608 * X ^ 3 - 131072 * X ^ 4) * ((891 * X ^ 2 + 891 * X ^ 3 - 20160 * X ^ 4 + 9360 * X ^ 5) * derivative ℚ (derivative ℚ G) + (13952 * X - 35780 * X ^ 2 - 117884 * X ^ 3 + 91616 * X ^ 4) * derivative ℚ G + (47768 - 288532 * X - 82428 * X ^ 2 + 147140 * X ^ 3) * G - (47768 + 20068 * X)) = 0 := by
    linear_combination (-891 * X - 4455 * X ^ 2 + 2340 * X ^ 3) * hd + (-6824 + 13830 * X + 3014 * X ^ 2) * h
  have hg : (65536 - 393216 * X + 655360 * X ^ 2 - 196608 * X ^ 3 - 131072 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (65536 : ℚ⟦X⟧) = 65536 := cnum 65536
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (256 * X ^ 8 + (0) * S) = 128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 891 + derivative ℚ (derivative ℚ G) * X * X * X * C 891 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-20160) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 9360 +
      derivative ℚ G * X * C 13952 + derivative ℚ G * X * X * C (-35780) +
      derivative ℚ G * X * X * X * C (-117884) + derivative ℚ G * X * X * X * X * C 91616 +
      G * C 47768 + G * X * C (-288532) +
      G * X * X * C (-82428) + G * X * X * X * C 147140 =
      C 47768 + C 20068 * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (256 * X ^ 8 + (0) * S) = 128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S) (m : ℕ) :
    891 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 891 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-20160) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 9360 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      13952 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-35780) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-117884) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 91616 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      47768 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-288532) * coeff (m + 1 + 1 + 1 + 1) G +
      (-82428) * coeff (m + 1 + 1 + 1) G + 147140 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (256 * X ^ 8 + (0) * S) = 128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S) :
    5346 * coeff (0 + 1 + 1 + 1) G + 1782 * coeff (0 + 1 + 1) G +
      41856 * coeff (0 + 1 + 1 + 1) G + (-71560) * coeff (0 + 1 + 1) G +
      (-117884) * coeff (0 + 1) G + 47768 * coeff (0 + 1 + 1 + 1) G +
      (-288532) * coeff (0 + 1 + 1) G + (-82428) * coeff (0 + 1) G +
      147140 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (256 * X ^ 8 + (0) * S) = 128 * X - 1024 * X ^ 2 + 2560 * X ^ 3 - 1920 * X ^ 4 - 256 * X ^ 5 + 256 * X ^ 6 + (-128 * X + 768 * X ^ 2 - 1280 * X ^ 3 + 384 * X ^ 4 + 256 * X ^ 5) * S) :
    10692 * coeff (0 + 1 + 1 + 1 + 1) G + 5346 * coeff (0 + 1 + 1 + 1) G +
      (-40320) * coeff (0 + 1 + 1) G + 55808 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-107340) * coeff (0 + 1 + 1 + 1) G + (-235768) * coeff (0 + 1 + 1) G +
      91616 * coeff (0 + 1) G + 47768 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-288532) * coeff (0 + 1 + 1 + 1) G + (-82428) * coeff (0 + 1 + 1) G +
      147140 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A071715Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071715.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A071715Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (7 * PowerSeries.X + 48 * PowerSeries.X ^ 4) * S + (-21 * PowerSeries.X - 48 * PowerSeries.X ^ 4) * S ^ 2 + (35 * PowerSeries.X + 16 * PowerSeries.X ^ 4) * S ^ 3 + (-35 * PowerSeries.X) * S ^ 4 + (21 * PowerSeries.X) * S ^ 5 + (-7 * PowerSeries.X) * S ^ 6 + (PowerSeries.X) * S ^ 7 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (12 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 5) * c * S + (-30 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c * S ^ 2 + (40 * PowerSeries.X ^ 2) * c * S ^ 3 + (-30 * PowerSeries.X ^ 2) * c * S ^ 4 + (12 * PowerSeries.X ^ 2) * c * S ^ 5 + (-2 * PowerSeries.X ^ 2) * c * S ^ 6 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (20 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 6) * c ^ 2 * S + (-40 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (40 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-20 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 4 - 128 * PowerSeries.X ^ 7) * c ^ 3 + (32 * PowerSeries.X ^ 4) * c ^ 3 * S + (-48 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 4 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (48 * PowerSeries.X ^ 5) * c ^ 4 * S + (-48 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (64 * PowerSeries.X ^ 6) * c ^ 5 * S + (-32 * PowerSeries.X ^ 6) * c ^ 5 * S ^ 2 + (-64 * PowerSeries.X ^ 7) * c ^ 6 + (64 * PowerSeries.X ^ 7) * c ^ 6 * S + (-128 * PowerSeries.X ^ 8) * c ^ 7) * hc - ((-127 * PowerSeries.X + 516 * PowerSeries.X ^ 2 - 496 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4 + 64 * PowerSeries.X ^ 5) + (120 * PowerSeries.X - 288 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4) * S + (-99 * PowerSeries.X + 120 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 - 16 * PowerSeries.X ^ 4) * S ^ 2 + (64 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 3 + (-29 * PowerSeries.X + 4 * PowerSeries.X ^ 2) * S ^ 4 + (8 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A071715Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (7 * PowerSeries.X + 48 * PowerSeries.X ^ 4) * S + (-21 * PowerSeries.X - 48 * PowerSeries.X ^ 4) * S ^ 2 + (35 * PowerSeries.X + 16 * PowerSeries.X ^ 4) * S ^ 3 + (-35 * PowerSeries.X) * S ^ 4 + (21 * PowerSeries.X) * S ^ 5 + (-7 * PowerSeries.X) * S ^ 6 + (PowerSeries.X) * S ^ 7 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (12 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 5) * c * S + (-30 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c * S ^ 2 + (40 * PowerSeries.X ^ 2) * c * S ^ 3 + (-30 * PowerSeries.X ^ 2) * c * S ^ 4 + (12 * PowerSeries.X ^ 2) * c * S ^ 5 + (-2 * PowerSeries.X ^ 2) * c * S ^ 6 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (20 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 6) * c ^ 2 * S + (-40 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (40 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-20 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 4 - 128 * PowerSeries.X ^ 7) * c ^ 3 + (32 * PowerSeries.X ^ 4) * c ^ 3 * S + (-48 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 4 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (48 * PowerSeries.X ^ 5) * c ^ 4 * S + (-48 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (64 * PowerSeries.X ^ 6) * c ^ 5 * S + (-32 * PowerSeries.X ^ 6) * c ^ 5 * S ^ 2 + (-64 * PowerSeries.X ^ 7) * c ^ 6 + (64 * PowerSeries.X ^ 7) * c ^ 6 * S + (-128 * PowerSeries.X ^ 8) * c ^ 7) * hc - ((-127 * PowerSeries.X + 516 * PowerSeries.X ^ 2 - 496 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4 + 64 * PowerSeries.X ^ 5) + (120 * PowerSeries.X - 288 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4) * S + (-99 * PowerSeries.X + 120 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 - 16 * PowerSeries.X ^ 4) * S ^ 2 + (64 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 3 + (-29 * PowerSeries.X + 4 * PowerSeries.X ^ 2) * S ^ 4 + (8 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6) * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A071715Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (256 * PowerSeries.X ^ 8) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (7 * PowerSeries.X + 48 * PowerSeries.X ^ 4) * S + (-21 * PowerSeries.X - 48 * PowerSeries.X ^ 4) * S ^ 2 + (35 * PowerSeries.X + 16 * PowerSeries.X ^ 4) * S ^ 3 + (-35 * PowerSeries.X) * S ^ 4 + (21 * PowerSeries.X) * S ^ 5 + (-7 * PowerSeries.X) * S ^ 6 + (PowerSeries.X) * S ^ 7 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (12 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 5) * c * S + (-30 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c * S ^ 2 + (40 * PowerSeries.X ^ 2) * c * S ^ 3 + (-30 * PowerSeries.X ^ 2) * c * S ^ 4 + (12 * PowerSeries.X ^ 2) * c * S ^ 5 + (-2 * PowerSeries.X ^ 2) * c * S ^ 6 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (20 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 6) * c ^ 2 * S + (-40 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (40 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-20 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 5 + (-8 * PowerSeries.X ^ 4 - 128 * PowerSeries.X ^ 7) * c ^ 3 + (32 * PowerSeries.X ^ 4) * c ^ 3 * S + (-48 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (32 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 4 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (48 * PowerSeries.X ^ 5) * c ^ 4 * S + (-48 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 3 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (64 * PowerSeries.X ^ 6) * c ^ 5 * S + (-32 * PowerSeries.X ^ 6) * c ^ 5 * S ^ 2 + (-64 * PowerSeries.X ^ 7) * c ^ 6 + (64 * PowerSeries.X ^ 7) * c ^ 6 * S + (-128 * PowerSeries.X ^ 8) * c ^ 7) * hc - ((-127 * PowerSeries.X + 516 * PowerSeries.X ^ 2 - 496 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4 + 64 * PowerSeries.X ^ 5) + (120 * PowerSeries.X - 288 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4) * S + (-99 * PowerSeries.X + 120 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 - 16 * PowerSeries.X ^ 4) * S ^ 2 + (64 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 3 + (-29 * PowerSeries.X + 4 * PowerSeries.X ^ 2) * S ^ 4 + (8 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6) * hS) m
      push_cast
      linear_combination r
