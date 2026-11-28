import OMAStatements.S_oeis_a165203

-- Problem: A165203: Expansion of (1+x)*c(x)^3/(1-x*c(x)^3), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a165203.lean:0 (declaration OMA.S_oeis_a165203.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A165203Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 4 - 8 * X - 12 * X ^ 2 + (-4 + 4 * X ^ 2) * S) :
    (4096 * X - 32768 * X ^ 2 + 57344 * X ^ 3 + 49152 * X ^ 4 - 61440 * X ^ 5 - 16384 * X ^ 6) * derivative ℚ G + (4096 - 40960 * X + 90112 * X ^ 2 + 16384 * X ^ 3 + 36864 * X ^ 4 - 8192 * X ^ 5) * G = 4096 - 32768 * X ^ 2 - 49152 * X ^ 3 - 20480 * X ^ 4 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-64 * X ^ 4 + 256 * X ^ 5 + 64 * X ^ 6) * G = (32 * X ^ 3 - 128 * X ^ 4 - 160 * X ^ 5 : ℚ⟦X⟧) + (-32 * X ^ 3 + 32 * X ^ 5) * S := by
    linear_combination (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 - (4 * X - 4 * X ^ 2) * S) * hG + (4 * X - 4 * X ^ 2) * ((4 * X - 4 * X ^ 2) * G - (-4 + 4 * X ^ 2)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-64 * (X * X * X * X) + 256 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-256 * X ^ 3 + 1280 * X ^ 4 + 384 * X ^ 5) * G + (-64 * X ^ 4 + 256 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d64, d256]
    ring
  have hR : derivative ℚ ((32 * (X * X * X) - 128 * (X * X * X * X) - 160 * (X * X * X * X * X) : ℚ⟦X⟧) + (-32 * (X * X * X) + 32 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      96 * X ^ 2 - 512 * X ^ 3 - 800 * X ^ 4 + (-96 * X ^ 2 + 160 * X ^ 4) * S + (-32 * X ^ 3 + 32 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d32, d128, d160]
    ring
  have hk2 : (-64 * (X * X * X * X) + 256 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (32 * (X * X * X) - 128 * (X * X * X * X) - 160 * (X * X * X * X * X) : ℚ⟦X⟧) + (-32 * (X * X * X) + 32 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-256 * X ^ 3 + 1280 * X ^ 4 + 384 * X ^ 5) * G + (-64 * X ^ 4 + 256 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G =
      96 * X ^ 2 - 512 * X ^ 3 - 800 * X ^ 4 + (-96 * X ^ 2 + 160 * X ^ 4) * S + (-32 * X ^ 3 + 32 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 6 * ((4096 * X - 32768 * X ^ 2 + 57344 * X ^ 3 + 49152 * X ^ 4 - 61440 * X ^ 5 - 16384 * X ^ 6) * derivative ℚ G + (4096 - 40960 * X + 90112 * X ^ 2 + 16384 * X ^ 3 + 36864 * X ^ 4 - 8192 * X ^ 5) * G - (4096 - 32768 * X ^ 2 - 49152 * X ^ 3 - 20480 * X ^ 4)) = 0 := by
    linear_combination (-32 * X ^ 3 + 32 * X ^ 5) ^ 2 * S * hdS - 2 * (-32 * X ^ 3 + 32 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-96 * X ^ 2 + 160 * X ^ 4) * (1 - 4 * X) + (-32 * X ^ 3 + 32 * X ^ 5) * (-4)) * hk + 2 * (-32 * X ^ 3 + 32 * X ^ 5) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 6 ≠ 0 := pow_ne_zero 6 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 4 - 8 * X - 12 * X ^ 2 + (-4 + 4 * X ^ 2) * S) :
    (5 * X ^ 2 + 5 * X ^ 3 - 285 * X ^ 4 + 695 * X ^ 5 + 180 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-21 * X + 89 * X ^ 2 - 353 * X ^ 3 + 1191 * X ^ 4 + 694 * X ^ 5) * derivative ℚ G + (-31 + 141 * X + 247 * X ^ 2 - 561 * X ^ 3 + 212 * X ^ 4) * G =
      -31 - 119 * X + 137 * X ^ 2 + 305 * X ^ 3 := by
  have h := key S G hS hG
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d8192 : derivative ℚ (8192 : ℚ⟦X⟧) = 0 := dnum 8192
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d20480 : derivative ℚ (20480 : ℚ⟦X⟧) = 0 := dnum 20480
  have d32768 : derivative ℚ (32768 : ℚ⟦X⟧) = 0 := dnum 32768
  have d36864 : derivative ℚ (36864 : ℚ⟦X⟧) = 0 := dnum 36864
  have d40960 : derivative ℚ (40960 : ℚ⟦X⟧) = 0 := dnum 40960
  have d49152 : derivative ℚ (49152 : ℚ⟦X⟧) = 0 := dnum 49152
  have d57344 : derivative ℚ (57344 : ℚ⟦X⟧) = 0 := dnum 57344
  have d61440 : derivative ℚ (61440 : ℚ⟦X⟧) = 0 := dnum 61440
  have d90112 : derivative ℚ (90112 : ℚ⟦X⟧) = 0 := dnum 90112
  have hL : derivative ℚ ((4096 * X - 32768 * (X * X) + 57344 * (X * X * X) + 49152 * (X * X * X * X) - 61440 * (X * X * X * X * X) - 16384 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (4096 - 40960 * X + 90112 * (X * X) + 16384 * (X * X * X) + 36864 * (X * X * X * X) - 8192 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (4096 - 65536 * X + 172032 * X ^ 2 + 196608 * X ^ 3 - 307200 * X ^ 4 - 98304 * X ^ 5) * derivative ℚ G + (4096 * X - 32768 * X ^ 2 + 57344 * X ^ 3 + 49152 * X ^ 4 - 61440 * X ^ 5 - 16384 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-40960 + 180224 * X + 49152 * X ^ 2 + 147456 * X ^ 3 - 40960 * X ^ 4) * G + (4096 - 40960 * X + 90112 * X ^ 2 + 16384 * X ^ 3 + 36864 * X ^ 4 - 8192 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d4096, d8192, d16384, d32768, d36864, d40960, d49152, d57344, d61440, d90112]
    ring
  have hRd : derivative ℚ (4096 - 32768 * (X * X) - 49152 * (X * X * X) - 20480 * (X * X * X * X) : ℚ⟦X⟧) = -65536 * X - 147456 * X ^ 2 - 81920 * X ^ 3 := by
    simp [Derivation.leibniz, d4096, d20480, d32768, d49152]
    ring
  have h2 : (4096 * X - 32768 * (X * X) + 57344 * (X * X * X) + 49152 * (X * X * X * X) - 61440 * (X * X * X * X * X) - 16384 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (4096 - 40960 * X + 90112 * (X * X) + 16384 * (X * X * X) + 36864 * (X * X * X * X) - 8192 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (4096 - 32768 * (X * X) - 49152 * (X * X * X) - 20480 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (4096 - 65536 * X + 172032 * X ^ 2 + 196608 * X ^ 3 - 307200 * X ^ 4 - 98304 * X ^ 5) * derivative ℚ G + (4096 * X - 32768 * X ^ 2 + 57344 * X ^ 3 + 49152 * X ^ 4 - 61440 * X ^ 5 - 16384 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-40960 + 180224 * X + 49152 * X ^ 2 + 147456 * X ^ 3 - 40960 * X ^ 4) * G + (4096 - 40960 * X + 90112 * X ^ 2 + 16384 * X ^ 3 + 36864 * X ^ 4 - 8192 * X ^ 5) * derivative ℚ G = -65536 * X - 147456 * X ^ 2 - 81920 * X ^ 3 := by
    rw [← hL, h2, hRd]
  have hfull : (4096 - 4096 * X ^ 2) * ((5 * X ^ 2 + 5 * X ^ 3 - 285 * X ^ 4 + 695 * X ^ 5 + 180 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-21 * X + 89 * X ^ 2 - 353 * X ^ 3 + 1191 * X ^ 4 + 694 * X ^ 5) * derivative ℚ G + (-31 + 141 * X + 247 * X ^ 2 - 561 * X ^ 3 + 212 * X ^ 4) * G - (-31 - 119 * X + 137 * X ^ 2 + 305 * X ^ 3)) = 0 := by
    linear_combination (5 * X + 45 * X ^ 2) * hd + (-31 - 119 * X) * h
  have hg : (4096 - 4096 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (4096 : ℚ⟦X⟧) = 4096 := cnum 4096
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 4 - 8 * X - 12 * X ^ 2 + (-4 + 4 * X ^ 2) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 5 + derivative ℚ (derivative ℚ G) * X * X * X * C 5 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-285) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 695 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 180 + derivative ℚ G * X * C (-21) +
      derivative ℚ G * X * X * C 89 + derivative ℚ G * X * X * X * C (-353) +
      derivative ℚ G * X * X * X * X * C 1191 + derivative ℚ G * X * X * X * X * X * C 694 +
      G * C (-31) + G * X * C 141 +
      G * X * X * C 247 + G * X * X * X * C (-561) +
      G * X * X * X * X * C 212 =
      C (-31) + C (-119) * X +
      C 137 * X * X + C 305 * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 4 - 8 * X - 12 * X ^ 2 + (-4 + 4 * X ^ 2) * S) (m : ℕ) :
    5 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 5 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-285) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 695 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      180 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-21) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      89 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-353) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      1191 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 694 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-31) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 141 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      247 * coeff (m + 1 + 1 + 1 + 1) G + (-561) * coeff (m + 1 + 1 + 1) G +
      212 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 4 - 8 * X - 12 * X ^ 2 + (-4 + 4 * X ^ 2) * S) :
    60 * coeff (0 + 1 + 1 + 1 + 1) G + 30 * coeff (0 + 1 + 1 + 1) G +
      (-570) * coeff (0 + 1 + 1) G + (-84) * coeff (0 + 1 + 1 + 1 + 1) G +
      267 * coeff (0 + 1 + 1 + 1) G + (-706) * coeff (0 + 1 + 1) G +
      1191 * coeff (0 + 1) G + (-31) * coeff (0 + 1 + 1 + 1 + 1) G +
      141 * coeff (0 + 1 + 1 + 1) G + 247 * coeff (0 + 1 + 1) G +
      (-561) * coeff (0 + 1) G + 212 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-4 * X + 12 * X ^ 2 + 8 * X ^ 3 + (4 * X - 4 * X ^ 2) * S) = 4 - 8 * X - 12 * X ^ 2 + (-4 + 4 * X ^ 2) * S) :
    100 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 60 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1710) * coeff (0 + 1 + 1 + 1) G + 1390 * coeff (0 + 1 + 1) G +
      (-105) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 356 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1059) * coeff (0 + 1 + 1 + 1) G + 2382 * coeff (0 + 1 + 1) G +
      694 * coeff (0 + 1) G + (-31) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      141 * coeff (0 + 1 + 1 + 1 + 1) G + 247 * coeff (0 + 1 + 1 + 1) G +
      (-561) * coeff (0 + 1 + 1) G + 212 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A165203Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a165203.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A165203Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X) * G + (2 + 2 * PowerSeries.X) * S + (2 * PowerSeries.X) * S * G + (-1 - PowerSeries.X) * S ^ 2 + (-PowerSeries.X) * S ^ 2 * G + (-2 * PowerSeries.X - 2 * PowerSeries.X ^ 2) * c + (-2 * PowerSeries.X ^ 2) * c * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2) * c * S + (2 * PowerSeries.X ^ 2) * c * S * G + (-4 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) * c ^ 2 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * G) * hc - ((-3 - 3 * PowerSeries.X) + (-3 * PowerSeries.X) * G + (1 + PowerSeries.X) * S + (PowerSeries.X) * S * G) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A165203Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X) * G + (2 + 2 * PowerSeries.X) * S + (2 * PowerSeries.X) * S * G + (-1 - PowerSeries.X) * S ^ 2 + (-PowerSeries.X) * S ^ 2 * G + (-2 * PowerSeries.X - 2 * PowerSeries.X ^ 2) * c + (-2 * PowerSeries.X ^ 2) * c * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2) * c * S + (2 * PowerSeries.X ^ 2) * c * S * G + (-4 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) * c ^ 2 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * G) * hc - ((-3 - 3 * PowerSeries.X) + (-3 * PowerSeries.X) * G + (1 + PowerSeries.X) * S + (PowerSeries.X) * S * G) * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A165203Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (8 * PowerSeries.X ^ 3) * hG - ((-1 - PowerSeries.X) + (-PowerSeries.X) * G + (2 + 2 * PowerSeries.X) * S + (2 * PowerSeries.X) * S * G + (-1 - PowerSeries.X) * S ^ 2 + (-PowerSeries.X) * S ^ 2 * G + (-2 * PowerSeries.X - 2 * PowerSeries.X ^ 2) * c + (-2 * PowerSeries.X ^ 2) * c * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2) * c * S + (2 * PowerSeries.X ^ 2) * c * S * G + (-4 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) * c ^ 2 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * G) * hc - ((-3 - 3 * PowerSeries.X) + (-3 * PowerSeries.X) * G + (1 + PowerSeries.X) * S + (PowerSeries.X) * S * G) * hS) m
      push_cast
      linear_combination r
