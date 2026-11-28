import OMAStatements.S_oeis_a110508

-- Problem: A110508: Expansion of 1/(1-(x+x^2)c(2x)), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a110508.lean:0 (declaration OMA.S_oeis_a110508.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A110508Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (3 * X - X ^ 2 + (X + X ^ 2) * S) = 4 * X + (0) * S) :
    (-64 + 448 * X + 384 * X ^ 2 + 832 * X ^ 3 + 1472 * X ^ 4 + 512 * X ^ 5) * derivative ℚ G + (-192 - 1024 * X + 1216 * X ^ 2 + 1664 * X ^ 3 + 768 * X ^ 4) * G = -256 - 1280 * X + 128 * X ^ 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 8 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (8 * X ^ 2 + 16 * X ^ 4 + 8 * X ^ 5) * G = (12 * X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) + (-4 * X ^ 2 - 4 * X ^ 3) * S := by
    linear_combination (3 * X - X ^ 2 - (X + X ^ 2) * S) * hG + (X + X ^ 2) * ((X + X ^ 2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 8 * X : ℚ⟦X⟧) = -8 := by
    simp [Derivation.leibniz, d8]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((8 * (X * X) + 16 * (X * X * X * X) + 8 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (16 * X + 64 * X ^ 3 + 40 * X ^ 4) * G + (8 * X ^ 2 + 16 * X ^ 4 + 8 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d8, d16]
    ring
  have hR : derivative ℚ ((12 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) + (-4 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * S) =
      24 * X - 12 * X ^ 2 + (-8 * X - 12 * X ^ 2) * S + (-4 * X ^ 2 - 4 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d12]
    ring
  have hk2 : (8 * (X * X) + 16 * (X * X * X * X) + 8 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (12 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) + (-4 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (16 * X + 64 * X ^ 3 + 40 * X ^ 4) * G + (8 * X ^ 2 + 16 * X ^ 4 + 8 * X ^ 5) * derivative ℚ G =
      24 * X - 12 * X ^ 2 + (-8 * X - 12 * X ^ 2) * S + (-4 * X ^ 2 - 4 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 4 * ((-64 + 448 * X + 384 * X ^ 2 + 832 * X ^ 3 + 1472 * X ^ 4 + 512 * X ^ 5) * derivative ℚ G + (-192 - 1024 * X + 1216 * X ^ 2 + 1664 * X ^ 3 + 768 * X ^ 4) * G - (-256 - 1280 * X + 128 * X ^ 2)) = 0 := by
    linear_combination (-4 * X ^ 2 - 4 * X ^ 3) ^ 2 * S * hdS - 2 * (-4 * X ^ 2 - 4 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-8 * X - 12 * X ^ 2) * (1 - 8 * X) + (-4 * X ^ 2 - 4 * X ^ 3) * (-8)) * hk + 2 * (-4 * X ^ 2 - 4 * X ^ 3) * (1 - 8 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 4 ≠ 0 := pow_ne_zero 4 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (3 * X - X ^ 2 + (X + X ^ 2) * S) = 4 * X + (0) * S) :
    (3 * X ^ 2 - 24 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 - 24 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-4 * X + 20 * X ^ 2 + 16 * X ^ 3 - 138 * X ^ 4 - 124 * X ^ 5) * derivative ℚ G + (-12 * X - 4 * X ^ 2 - 34 * X ^ 3 - 96 * X ^ 4) * G =
      -16 * X - 4 * X ^ 2 := by
  have h := key S G hS hG
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d448 : derivative ℚ (448 : ℚ⟦X⟧) = 0 := dnum 448
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d832 : derivative ℚ (832 : ℚ⟦X⟧) = 0 := dnum 832
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1216 : derivative ℚ (1216 : ℚ⟦X⟧) = 0 := dnum 1216
  have d1280 : derivative ℚ (1280 : ℚ⟦X⟧) = 0 := dnum 1280
  have d1472 : derivative ℚ (1472 : ℚ⟦X⟧) = 0 := dnum 1472
  have d1664 : derivative ℚ (1664 : ℚ⟦X⟧) = 0 := dnum 1664
  have hL : derivative ℚ ((-64 + 448 * X + 384 * (X * X) + 832 * (X * X * X) + 1472 * (X * X * X * X) + 512 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-192 - 1024 * X + 1216 * (X * X) + 1664 * (X * X * X) + 768 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (448 + 768 * X + 2496 * X ^ 2 + 5888 * X ^ 3 + 2560 * X ^ 4) * derivative ℚ G + (-64 + 448 * X + 384 * X ^ 2 + 832 * X ^ 3 + 1472 * X ^ 4 + 512 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-1024 + 2432 * X + 4992 * X ^ 2 + 3072 * X ^ 3) * G + (-192 - 1024 * X + 1216 * X ^ 2 + 1664 * X ^ 3 + 768 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d64, d192, d384, d448, d512, d768, d832, d1024, d1216, d1472, d1664]
    ring
  have hRd : derivative ℚ (-256 - 1280 * X + 128 * (X * X) : ℚ⟦X⟧) = -1280 + 256 * X := by
    simp [Derivation.leibniz, d128, d256, d1280]
    ring
  have h2 : (-64 + 448 * X + 384 * (X * X) + 832 * (X * X * X) + 1472 * (X * X * X * X) + 512 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-192 - 1024 * X + 1216 * (X * X) + 1664 * (X * X * X) + 768 * (X * X * X * X) : ℚ⟦X⟧) * G = (-256 - 1280 * X + 128 * (X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (448 + 768 * X + 2496 * X ^ 2 + 5888 * X ^ 3 + 2560 * X ^ 4) * derivative ℚ G + (-64 + 448 * X + 384 * X ^ 2 + 832 * X ^ 3 + 1472 * X ^ 4 + 512 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-1024 + 2432 * X + 4992 * X ^ 2 + 3072 * X ^ 3) * G + (-192 - 1024 * X + 1216 * X ^ 2 + 1664 * X ^ 3 + 768 * X ^ 4) * derivative ℚ G = -1280 + 256 * X := by
    rw [← hL, h2, hRd]
  have hfull : (64 + 64 * X) * ((3 * X ^ 2 - 24 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 - 24 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-4 * X + 20 * X ^ 2 + 16 * X ^ 3 - 138 * X ^ 4 - 124 * X ^ 5) * derivative ℚ G + (-12 * X - 4 * X ^ 2 - 34 * X ^ 3 - 96 * X ^ 4) * G - (-16 * X - 4 * X ^ 2)) = 0 := by
    linear_combination (-3 * X ^ 2) * hd + (4 * X) * h
  have hg : (64 + 64 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (64 : ℚ⟦X⟧) = 64 := cnum 64
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (3 * X - X ^ 2 + (X + X ^ 2) * S) = 4 * X + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 3 + derivative ℚ (derivative ℚ G) * X * X * X * C (-24) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 6 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-45) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-24) + derivative ℚ G * X * C (-4) +
      derivative ℚ G * X * X * C 20 + derivative ℚ G * X * X * X * C 16 +
      derivative ℚ G * X * X * X * X * C (-138) + derivative ℚ G * X * X * X * X * X * C (-124) +
      G * X * C (-12) + G * X * X * C (-4) +
      G * X * X * X * C (-34) + G * X * X * X * X * C (-96) =
      C (-16) * X + C (-4) * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (3 * X - X ^ 2 + (X + X ^ 2) * S) = 4 * X + (0) * S) (m : ℕ) :
    3 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-24) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      6 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-45) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-24) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-4) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      20 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-138) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-124) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-12) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-34) * coeff (m + 1 + 1 + 1) G + (-96) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (3 * X - X ^ 2 + (X + X ^ 2) * S) = 4 * X + (0) * S) :
    36 * coeff (0 + 1 + 1 + 1 + 1) G + (-144) * coeff (0 + 1 + 1 + 1) G +
      12 * coeff (0 + 1 + 1) G + (-16) * coeff (0 + 1 + 1 + 1 + 1) G +
      60 * coeff (0 + 1 + 1 + 1) G + 32 * coeff (0 + 1 + 1) G +
      (-138) * coeff (0 + 1) G + (-12) * coeff (0 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1) G + (-34) * coeff (0 + 1) G +
      (-96) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (3 * X - X ^ 2 + (X + X ^ 2) * S) = 4 * X + (0) * S) :
    60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-288) * coeff (0 + 1 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1 + 1) G + (-90) * coeff (0 + 1 + 1) G +
      (-20) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 80 * coeff (0 + 1 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1 + 1) G + (-276) * coeff (0 + 1 + 1) G +
      (-124) * coeff (0 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1) G + (-34) * coeff (0 + 1 + 1) G +
      (-96) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A110508Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110508.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A110508Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (4 * PowerSeries.X) * hG - ((-PowerSeries.X - PowerSeries.X ^ 2) * G) * hc)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A110508Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (4 * PowerSeries.X) * hG - ((-PowerSeries.X - PowerSeries.X ^ 2) * G) * hc)
      push_cast
      linear_combination r
    | succ m =>
      have r := A110508Aux.rel (S) G (by linear_combination hS)
          (by linear_combination (4 * PowerSeries.X) * hG - ((-PowerSeries.X - PowerSeries.X ^ 2) * G) * hc) m
      push_cast
      linear_combination r
