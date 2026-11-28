import OMAStatements.S_oeis_a247173

-- Problem: A247173: Expansion of g.f. (-1)/(2*x^2+2*x) +(-2*x^3-3*x^2+1) / (sqrt(x^4+4*x^3-2*x^2-4*x+1)*(2*x^2+2*x)).
-- Upstream: formal-conjectures statements/oeis-a247173.lean:0 (declaration OMA.S_oeis_a247173.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A247173Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X + 2 * X ^ 2) * S) = 1 - 3 * X ^ 2 - 2 * X ^ 3 + (-1) * S) :
    (16 * X - 80 * X ^ 2 + 224 * X ^ 4 + 16 * X ^ 5 - 144 * X ^ 6 - 32 * X ^ 7) * derivative ℚ G + (16 - 96 * X + 128 * X ^ 3 - 48 * X ^ 4 - 96 * X ^ 5 - 32 * X ^ 6) * G = 16 - 64 * X + 160 * X ^ 2 - 64 * X ^ 3 - 16 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d28 : derivative ℚ (28 : ℚ⟦X⟧) = 0 := dnum 28
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have hS2 : S * S = (1 - 4 * X - 2 * (X * X) + 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 2 + 8 * X ^ 3 + 36 * X ^ 4 + 16 * X ^ 5 - 28 * X ^ 6 - 24 * X ^ 7 - 4 * X ^ 8) * G = (2 * X - 6 * X ^ 2 - 12 * X ^ 3 + 4 * X ^ 4 + 10 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) + (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) * S := by
    linear_combination (0 - (2 * X + 2 * X ^ 2) * S) * hG + (2 * X + 2 * X ^ 2) * ((2 * X + 2 * X ^ 2) * G - (-1)) * hS
  have hPd : derivative ℚ (1 - 4 * X - 2 * (X * X) + 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -4 - 4 * X + 12 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 - 4 * X + 12 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X) + 8 * (X * X * X) + 36 * (X * X * X * X) + 16 * (X * X * X * X * X) - 28 * (X * X * X * X * X * X) - 24 * (X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-8 * X + 24 * X ^ 2 + 144 * X ^ 3 + 80 * X ^ 4 - 168 * X ^ 5 - 168 * X ^ 6 - 32 * X ^ 7) * G + (-4 * X ^ 2 + 8 * X ^ 3 + 36 * X ^ 4 + 16 * X ^ 5 - 28 * X ^ 6 - 24 * X ^ 7 - 4 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d16, d24, d28, d36]
    ring
  have hR : derivative ℚ ((2 * X - 6 * (X * X) - 12 * (X * X * X) + 4 * (X * X * X * X) + 10 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-2 * X - 2 * (X * X) + 6 * (X * X * X) + 10 * (X * X * X * X) + 4 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      2 - 12 * X - 36 * X ^ 2 + 16 * X ^ 3 + 50 * X ^ 4 + 12 * X ^ 5 + (-2 - 4 * X + 18 * X ^ 2 + 40 * X ^ 3 + 20 * X ^ 4) * S + (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d6, d10, d12]
    ring
  have hk2 : (-4 * (X * X) + 8 * (X * X * X) + 36 * (X * X * X * X) + 16 * (X * X * X * X * X) - 28 * (X * X * X * X * X * X) - 24 * (X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * X - 6 * (X * X) - 12 * (X * X * X) + 4 * (X * X * X * X) + 10 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-2 * X - 2 * (X * X) + 6 * (X * X * X) + 10 * (X * X * X * X) + 4 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X + 24 * X ^ 2 + 144 * X ^ 3 + 80 * X ^ 4 - 168 * X ^ 5 - 168 * X ^ 6 - 32 * X ^ 7) * G + (-4 * X ^ 2 + 8 * X ^ 3 + 36 * X ^ 4 + 16 * X ^ 5 - 28 * X ^ 6 - 24 * X ^ 7 - 4 * X ^ 8) * derivative ℚ G =
      2 - 12 * X - 36 * X ^ 2 + 16 * X ^ 3 + 50 * X ^ 4 + 12 * X ^ 5 + (-2 - 4 * X + 18 * X ^ 2 + 40 * X ^ 3 + 20 * X ^ 4) * S + (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 12 * X ^ 2 - 24 * X ^ 3 - 10 * X ^ 4 + 16 * X ^ 5 + 20 * X ^ 6 + 8 * X ^ 7 + X ^ 8) * ((16 * X - 80 * X ^ 2 + 224 * X ^ 4 + 16 * X ^ 5 - 144 * X ^ 6 - 32 * X ^ 7) * derivative ℚ G + (16 - 96 * X + 128 * X ^ 3 - 48 * X ^ 4 - 96 * X ^ 5 - 32 * X ^ 6) * G - (16 - 64 * X + 160 * X ^ 2 - 64 * X ^ 3 - 16 * X ^ 4))) = 0 := by
    linear_combination (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) ^ 2 * S * hdS - 2 * (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 - 4 * X + 18 * X ^ 2 + 40 * X ^ 3 + 20 * X ^ 4) * (1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4) + (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) * (-4 - 4 * X + 12 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-2 * X - 2 * X ^ 2 + 6 * X ^ 3 + 10 * X ^ 4 + 4 * X ^ 5) * (1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 12 * X ^ 2 - 24 * X ^ 3 - 10 * X ^ 4 + 16 * X ^ 5 + 20 * X ^ 6 + 8 * X ^ 7 + X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X + 2 * X ^ 2) * S) = 1 - 3 * X ^ 2 - 2 * X ^ 3 + (-1) * S) :
    (-3 * X ^ 2 + 9 * X ^ 3 + 18 * X ^ 4 - 6 * X ^ 5 - 15 * X ^ 6 - 3 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-2 * X + 24 * X ^ 2 + 48 * X ^ 3 - 40 * X ^ 4 - 82 * X ^ 5 - 20 * X ^ 6) * derivative ℚ G + (4 + 2 * X + 4 * X ^ 2 - 32 * X ^ 3 - 40 * X ^ 4 - 14 * X ^ 5) * G =
      4 + 4 * X - 12 * X ^ 2 - 4 * X ^ 3 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d144 : derivative ℚ (144 : ℚ⟦X⟧) = 0 := dnum 144
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d224 : derivative ℚ (224 : ℚ⟦X⟧) = 0 := dnum 224
  have hL : derivative ℚ ((16 * X - 80 * (X * X) + 224 * (X * X * X * X) + 16 * (X * X * X * X * X) - 144 * (X * X * X * X * X * X) - 32 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 96 * X + 128 * (X * X * X) - 48 * (X * X * X * X) - 96 * (X * X * X * X * X) - 32 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (16 - 160 * X + 896 * X ^ 3 + 80 * X ^ 4 - 864 * X ^ 5 - 224 * X ^ 6) * derivative ℚ G + (16 * X - 80 * X ^ 2 + 224 * X ^ 4 + 16 * X ^ 5 - 144 * X ^ 6 - 32 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-96 + 384 * X ^ 2 - 192 * X ^ 3 - 480 * X ^ 4 - 192 * X ^ 5) * G + (16 - 96 * X + 128 * X ^ 3 - 48 * X ^ 4 - 96 * X ^ 5 - 32 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d32, d48, d80, d96, d128, d144, d224]
    ring
  have hRd : derivative ℚ (16 - 64 * X + 160 * (X * X) - 64 * (X * X * X) - 16 * (X * X * X * X) : ℚ⟦X⟧) = -64 + 320 * X - 192 * X ^ 2 - 64 * X ^ 3 := by
    simp [Derivation.leibniz, d16, d64, d160]
    ring
  have h2 : (16 * X - 80 * (X * X) + 224 * (X * X * X * X) + 16 * (X * X * X * X * X) - 144 * (X * X * X * X * X * X) - 32 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 96 * X + 128 * (X * X * X) - 48 * (X * X * X * X) - 96 * (X * X * X * X * X) - 32 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (16 - 64 * X + 160 * (X * X) - 64 * (X * X * X) - 16 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (16 - 160 * X + 896 * X ^ 3 + 80 * X ^ 4 - 864 * X ^ 5 - 224 * X ^ 6) * derivative ℚ G + (16 * X - 80 * X ^ 2 + 224 * X ^ 4 + 16 * X ^ 5 - 144 * X ^ 6 - 32 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-96 + 384 * X ^ 2 - 192 * X ^ 3 - 480 * X ^ 4 - 192 * X ^ 5) * G + (16 - 96 * X + 128 * X ^ 3 - 48 * X ^ 4 - 96 * X ^ 5 - 32 * X ^ 6) * derivative ℚ G = -64 + 320 * X - 192 * X ^ 2 - 64 * X ^ 3 := by
    rw [← hL, h2, hRd]
  have hfull : (16 - 32 * X) * ((-3 * X ^ 2 + 9 * X ^ 3 + 18 * X ^ 4 - 6 * X ^ 5 - 15 * X ^ 6 - 3 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-2 * X + 24 * X ^ 2 + 48 * X ^ 3 - 40 * X ^ 4 - 82 * X ^ 5 - 20 * X ^ 6) * derivative ℚ G + (4 + 2 * X + 4 * X ^ 2 - 32 * X ^ 3 - 40 * X ^ 4 - 14 * X ^ 5) * G - (4 + 4 * X - 12 * X ^ 2 - 4 * X ^ 3)) = 0 := by
    linear_combination (-3 * X) * hd + (4) * h
  have hg : (16 - 32 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X + 2 * X ^ 2) * S) = 1 - 3 * X ^ 2 - 2 * X ^ 3 + (-1) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C (-3) + derivative ℚ (derivative ℚ G) * X * X * X * C 9 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 18 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-6) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-15) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-3) +
      derivative ℚ G * X * C (-2) + derivative ℚ G * X * X * C 24 +
      derivative ℚ G * X * X * X * C 48 + derivative ℚ G * X * X * X * X * C (-40) +
      derivative ℚ G * X * X * X * X * X * C (-82) + derivative ℚ G * X * X * X * X * X * X * C (-20) +
      G * C 4 + G * X * C 2 +
      G * X * X * C 4 + G * X * X * X * C (-32) +
      G * X * X * X * X * C (-40) + G * X * X * X * X * X * C (-14) =
      C 4 + C 4 * X +
      C (-12) * X * X + C (-4) * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X + 2 * X ^ 2) * S) = 1 - 3 * X ^ 2 - 2 * X ^ 3 + (-1) * S) (m : ℕ) :
    (-3) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 9 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      18 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-15) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-2) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 24 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      48 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-40) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-82) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-20) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-32) * coeff (m + 1 + 1 + 1 + 1) G +
      (-40) * coeff (m + 1 + 1 + 1) G + (-14) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X + 2 * X ^ 2) * S) = 1 - 3 * X ^ 2 - 2 * X ^ 3 + (-1) * S) :
    (-60) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 108 * coeff (0 + 1 + 1 + 1 + 1) G +
      108 * coeff (0 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1) G +
      (-10) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 96 * coeff (0 + 1 + 1 + 1 + 1) G +
      144 * coeff (0 + 1 + 1 + 1) G + (-80) * coeff (0 + 1 + 1) G +
      (-82) * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      2 * coeff (0 + 1 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1) G + (-40) * coeff (0 + 1) G +
      (-14) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X + 2 * X ^ 2) * S) = 1 - 3 * X ^ 2 - 2 * X ^ 3 + (-1) * S) :
    (-90) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 180 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      216 * coeff (0 + 1 + 1 + 1 + 1) G + (-36) * coeff (0 + 1 + 1 + 1) G +
      (-30) * coeff (0 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-120) * coeff (0 + 1 + 1 + 1) G + (-164) * coeff (0 + 1 + 1) G +
      (-20) * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1 + 1) G + (-40) * coeff (0 + 1 + 1) G +
      (-14) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A247173Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a247173.main := by
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
    have r := A247173Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A247173Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A247173Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
