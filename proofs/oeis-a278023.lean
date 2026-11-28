import OMAStatements.S_oeis_a278023

-- Problem: A278023: G.f.: 2*x*(1-x*sqrt(1-4*x))/((1+2*x^2+sqrt(1-4*x))*sqrt(1-4*x)).
-- Upstream: formal-conjectures statements/oeis-a278023.lean:0 (declaration OMA.S_oeis_a278023.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A278023Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (1 + 2 * X ^ 2) * S) = 2 * X + (-2 * X ^ 2) * S) :
    (16 - 32 * X - 144 * X ^ 2 + 48 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 128 * X ^ 6) * derivative ℚ G + (-32 - 144 * X ^ 2 - 256 * X ^ 3 - 192 * X ^ 4 + 192 * X ^ 5) * G = 16 + 48 * X ^ 2 + 224 * X ^ 3 + 192 * X ^ 4 - 192 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X + 12 * X ^ 2 + 16 * X ^ 3 - 4 * X ^ 4 + 16 * X ^ 5) * G = (2 * X - 6 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 - 16 * X ^ 5 : ℚ⟦X⟧) + (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) * S := by
    linear_combination (1 - 4 * X - (1 + 2 * X ^ 2) * S) * hG + (1 + 2 * X ^ 2) * ((1 + 2 * X ^ 2) * G - (-2 * X ^ 2)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * X + 12 * (X * X) + 16 * (X * X * X) - 4 * (X * X * X * X) + 16 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (-4 + 24 * X + 48 * X ^ 2 - 16 * X ^ 3 + 80 * X ^ 4) * G + (-4 * X + 12 * X ^ 2 + 16 * X ^ 3 - 4 * X ^ 4 + 16 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d12, d16]
    ring
  have hR : derivative ℚ ((2 * X - 6 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) - 16 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * X - 2 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * S) =
      2 - 12 * X - 24 * X ^ 2 + 16 * X ^ 3 - 80 * X ^ 4 + (-2 - 4 * X + 12 * X ^ 2) * S + (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d16]
    ring
  have hk2 : (-4 * X + 12 * (X * X) + 16 * (X * X * X) - 4 * (X * X * X * X) + 16 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * X - 6 * (X * X) - 8 * (X * X * X) + 4 * (X * X * X * X) - 16 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * X - 2 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-4 + 24 * X + 48 * X ^ 2 - 16 * X ^ 3 + 80 * X ^ 4) * G + (-4 * X + 12 * X ^ 2 + 16 * X ^ 3 - 4 * X ^ 4 + 16 * X ^ 5) * derivative ℚ G =
      2 - 12 * X - 24 * X ^ 2 + 16 * X ^ 3 - 80 * X ^ 4 + (-2 - 4 * X + 12 * X ^ 2) * S + (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 4 * X) * ((16 - 32 * X - 144 * X ^ 2 + 48 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 128 * X ^ 6) * derivative ℚ G + (-32 - 144 * X ^ 2 - 256 * X ^ 3 - 192 * X ^ 4 + 192 * X ^ 5) * G - (16 + 48 * X ^ 2 + 224 * X ^ 3 + 192 * X ^ 4 - 192 * X ^ 5))) = 0 := by
    linear_combination (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) ^ 2 * S * hdS - 2 * (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 - 4 * X + 12 * X ^ 2) * (1 - 4 * X) + (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) * (-4)) * hk + 2 * (-2 * X - 2 * X ^ 2 + 4 * X ^ 3) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (1 + 2 * X ^ 2) * S) = 2 * X + (-2 * X ^ 2) * S) :
    (3 * X ^ 3 - 9 * X ^ 4 - 12 * X ^ 5 + 3 * X ^ 6 - 12 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-3 * X ^ 2 - 12 * X ^ 3 - 54 * X ^ 4 + 24 * X ^ 5 - 126 * X ^ 6) * derivative ℚ (derivative ℚ G) + (2 * X + 6 * X ^ 2 - 26 * X ^ 3 + 38 * X ^ 4 - 314 * X ^ 5) * derivative ℚ G + (-4 * X + 4 * X ^ 2 + 6 * X ^ 3 - 156 * X ^ 4) * G =
      2 * X - 2 * X ^ 2 - 6 * X ^ 3 + 156 * X ^ 4 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d144 : derivative ℚ (144 : ℚ⟦X⟧) = 0 := dnum 144
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d224 : derivative ℚ (224 : ℚ⟦X⟧) = 0 := dnum 224
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d288 : derivative ℚ (288 : ℚ⟦X⟧) = 0 := dnum 288
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have d480 : derivative ℚ (480 : ℚ⟦X⟧) = 0 := dnum 480
  have d672 : derivative ℚ (672 : ℚ⟦X⟧) = 0 := dnum 672
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d960 : derivative ℚ (960 : ℚ⟦X⟧) = 0 := dnum 960
  have hL : derivative ℚ ((16 - 32 * X - 144 * (X * X) + 48 * (X * X * X) + 80 * (X * X * X * X) - 96 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-32 - 144 * (X * X) - 256 * (X * X * X) - 192 * (X * X * X * X) + 192 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (-32 - 288 * X + 144 * X ^ 2 + 320 * X ^ 3 - 480 * X ^ 4 + 768 * X ^ 5) * derivative ℚ G + (16 - 32 * X - 144 * X ^ 2 + 48 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-288 * X - 768 * X ^ 2 - 768 * X ^ 3 + 960 * X ^ 4) * G + (-32 - 144 * X ^ 2 - 256 * X ^ 3 - 192 * X ^ 4 + 192 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d32, d48, d80, d96, d128, d144, d192, d256]
    ring
  have hRd : derivative ℚ (16 + 48 * (X * X) + 224 * (X * X * X) + 192 * (X * X * X * X) - 192 * (X * X * X * X * X) : ℚ⟦X⟧) = 96 * X + 672 * X ^ 2 + 768 * X ^ 3 - 960 * X ^ 4 := by
    simp [Derivation.leibniz, d16, d48, d192, d224]
    ring
  have h2 : (16 - 32 * X - 144 * (X * X) + 48 * (X * X * X) + 80 * (X * X * X * X) - 96 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-32 - 144 * (X * X) - 256 * (X * X * X) - 192 * (X * X * X * X) + 192 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (16 + 48 * (X * X) + 224 * (X * X * X) + 192 * (X * X * X * X) - 192 * (X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-32 - 288 * X + 144 * X ^ 2 + 320 * X ^ 3 - 480 * X ^ 4 + 768 * X ^ 5) * derivative ℚ G + (16 - 32 * X - 144 * X ^ 2 + 48 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-288 * X - 768 * X ^ 2 - 768 * X ^ 3 + 960 * X ^ 4) * G + (-32 - 144 * X ^ 2 - 256 * X ^ 3 - 192 * X ^ 4 + 192 * X ^ 5) * derivative ℚ G = 96 * X + 672 * X ^ 2 + 768 * X ^ 3 - 960 * X ^ 4 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((-32 - 288 * X + 144 * (X * X) + 320 * (X * X * X) - 480 * (X * X * X * X) + 768 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 32 * X - 144 * (X * X) + 48 * (X * X * X) + 80 * (X * X * X * X) - 96 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-288 * X - 768 * (X * X) - 768 * (X * X * X) + 960 * (X * X * X * X) : ℚ⟦X⟧) * G + (-32 - 144 * (X * X) - 256 * (X * X * X) - 192 * (X * X * X * X) + 192 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-288 - 288 * X - 576 * X ^ 2 - 3456 * X ^ 3 + 5760 * X ^ 4) * derivative ℚ G + (-96 - 576 * X + 144 * X ^ 2 + 384 * X ^ 3 - 1152 * X ^ 4 + 1728 * X ^ 5) * derivative ℚ (derivative ℚ G) + (16 - 32 * X - 144 * X ^ 2 + 48 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-288 - 1536 * X - 2304 * X ^ 2 + 3840 * X ^ 3) * G := by
    simp [Derivation.leibniz, d16, d32, d48, d80, d96, d128, d144, d192, d256, d288, d320, d480, d768, d960]
    ring
  have hRd2 : derivative ℚ (96 * X + 672 * (X * X) + 768 * (X * X * X) - 960 * (X * X * X * X) : ℚ⟦X⟧) = 96 + 1344 * X + 2304 * X ^ 2 - 3840 * X ^ 3 := by
    simp [Derivation.leibniz, d96, d672, d768, d960]
    ring
  have hdp : (-32 - 288 * X + 144 * (X * X) + 320 * (X * X * X) - 480 * (X * X * X * X) + 768 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 32 * X - 144 * (X * X) + 48 * (X * X * X) + 80 * (X * X * X * X) - 96 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-288 * X - 768 * (X * X) - 768 * (X * X * X) + 960 * (X * X * X * X) : ℚ⟦X⟧) * G + (-32 - 144 * (X * X) - 256 * (X * X * X) - 192 * (X * X * X * X) + 192 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (96 * X + 672 * (X * X) + 768 * (X * X * X) - 960 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-288 - 288 * X - 576 * X ^ 2 - 3456 * X ^ 3 + 5760 * X ^ 4) * derivative ℚ G + (-96 - 576 * X + 144 * X ^ 2 + 384 * X ^ 3 - 1152 * X ^ 4 + 1728 * X ^ 5) * derivative ℚ (derivative ℚ G) + (16 - 32 * X - 144 * X ^ 2 + 48 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-288 - 1536 * X - 2304 * X ^ 2 + 3840 * X ^ 3) * G = 96 + 1344 * X + 2304 * X ^ 2 - 3840 * X ^ 3 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (16 + 32 * X - 48 * X ^ 2 - 64 * X ^ 3 + 64 * X ^ 4) * ((3 * X ^ 3 - 9 * X ^ 4 - 12 * X ^ 5 + 3 * X ^ 6 - 12 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-3 * X ^ 2 - 12 * X ^ 3 - 54 * X ^ 4 + 24 * X ^ 5 - 126 * X ^ 6) * derivative ℚ (derivative ℚ G) + (2 * X + 6 * X ^ 2 - 26 * X ^ 3 + 38 * X ^ 4 - 314 * X ^ 5) * derivative ℚ G + (-4 * X + 4 * X ^ 2 + 6 * X ^ 3 - 156 * X ^ 4) * G - (2 * X - 2 * X ^ 2 - 6 * X ^ 3 + 156 * X ^ 4)) = 0 := by
    linear_combination (3 * X ^ 3 + 3 * X ^ 4 - 6 * X ^ 5) * hd2 + (-3 * X ^ 2 - 6 * X ^ 3 + 18 * X ^ 4) * hd + (2 * X + 2 * X ^ 2 - 22 * X ^ 3) * h
  have hg : (16 + 32 * X - 48 * X ^ 2 - 64 * X ^ 3 + 64 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (1 + 2 * X ^ 2) * S) = 2 * X + (-2 * X ^ 2) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 3 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-9) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 3 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ G) * X * X * C (-3) +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-12) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-54) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 24 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-126) +
      derivative ℚ G * X * C 2 + derivative ℚ G * X * X * C 6 +
      derivative ℚ G * X * X * X * C (-26) + derivative ℚ G * X * X * X * X * C 38 +
      derivative ℚ G * X * X * X * X * X * C (-314) + G * X * C (-4) +
      G * X * X * C 4 + G * X * X * X * C 6 +
      G * X * X * X * X * C (-156) =
      C 2 * X + C (-2) * X * X +
      C (-6) * X * X * X + C 156 * X * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (1 + 2 * X ^ 2) * S) = 2 * X + (-2 * X ^ 2) * S) (m : ℕ) :
    3 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 3 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-54) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      24 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-126) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 6 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-26) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 38 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-314) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 6 * coeff (m + 1 + 1 + 1 + 1) G +
      (-156) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (1 + 2 * X ^ 2) * S) = 2 * X + (-2 * X ^ 2) * S) :
    180 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-216) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-72) * coeff (0 + 1 + 1 + 1) G + (-60) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-144) * coeff (0 + 1 + 1 + 1 + 1) G + (-324) * coeff (0 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1) G + 10 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      24 * coeff (0 + 1 + 1 + 1 + 1) G + (-78) * coeff (0 + 1 + 1 + 1) G +
      76 * coeff (0 + 1 + 1) G + (-314) * coeff (0 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1) G + (-156) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (1 + 2 * X ^ 2) * S) = 2 * X + (-2 * X ^ 2) * S) :
    360 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-540) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-288) * coeff (0 + 1 + 1 + 1 + 1) G + 18 * coeff (0 + 1 + 1 + 1) G +
      (-90) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-240) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-648) * coeff (0 + 1 + 1 + 1 + 1) G + 144 * coeff (0 + 1 + 1 + 1) G +
      (-252) * coeff (0 + 1 + 1) G + 12 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      30 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-104) * coeff (0 + 1 + 1 + 1 + 1) G +
      114 * coeff (0 + 1 + 1 + 1) G + (-628) * coeff (0 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1) G + (-156) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A278023Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278023.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A278023Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (1) * hG - ((1) * G) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A278023Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (1) * hG - ((1) * G) * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A278023Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (1) * hG - ((1) * G) * hS) m
      push_cast
      linear_combination r
