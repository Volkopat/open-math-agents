import OMAStatements.S_oeis_a240688

-- Problem: A240688: Expansion of -(x*sqrt(-4*x^2-4*x+1)-2*x^2-3*x) / ((x+1)*sqrt(-4*x^2-4*x+1)+ 4*x^3+8*x^2+3*x-1).
-- Upstream: formal-conjectures statements/oeis-a240688.lean:0 (declaration OMA.S_oeis_a240688.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A240688Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2)
    (hG : G * (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 + (1 + X) * S) = 3 * X + 2 * X ^ 2 + (-X) * S) :
    (16 - 16 * X - 224 * X ^ 2 - 320 * X ^ 3 - 128 * X ^ 4) * derivative ℚ G + (-48 - 96 * X - 192 * X ^ 2 - 128 * X ^ 3) * G = -32 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d22 : derivative ℚ (22 : ℚ⟦X⟧) = 0 := dnum 22
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d52 : derivative ℚ (52 : ℚ⟦X⟧) = 0 := dnum 52
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d92 : derivative ℚ (92 : ℚ⟦X⟧) = 0 := dnum 92
  have hS2 : S * S = (1 - 4 * X - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X + 4 * X ^ 2 + 52 * X ^ 3 + 92 * X ^ 4 + 64 * X ^ 5 + 16 * X ^ 6) * G = (-2 * X + 4 * X ^ 2 + 22 * X ^ 3 + 24 * X ^ 4 + 8 * X ^ 5 : ℚ⟦X⟧) + (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) * S := by
    linear_combination (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 - (1 + X) * S) * hG + (1 + X) * ((1 + X) * G - (-X)) * hS
  have hPd : derivative ℚ (1 - 4 * X - 4 * (X * X) : ℚ⟦X⟧) = -4 - 8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 - 8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * X + 4 * (X * X) + 52 * (X * X * X) + 92 * (X * X * X * X) + 64 * (X * X * X * X * X) + 16 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-4 + 8 * X + 156 * X ^ 2 + 368 * X ^ 3 + 320 * X ^ 4 + 96 * X ^ 5) * G + (-4 * X + 4 * X ^ 2 + 52 * X ^ 3 + 92 * X ^ 4 + 64 * X ^ 5 + 16 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d16, d52, d64, d92]
    ring
  have hR : derivative ℚ ((-2 * X + 4 * (X * X) + 22 * (X * X * X) + 24 * (X * X * X * X) + 8 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * X - 8 * (X * X) - 10 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      -2 + 8 * X + 66 * X ^ 2 + 96 * X ^ 3 + 40 * X ^ 4 + (-2 - 16 * X - 30 * X ^ 2 - 16 * X ^ 3) * S + (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8, d10, d22, d24]
    ring
  have hk2 : (-4 * X + 4 * (X * X) + 52 * (X * X * X) + 92 * (X * X * X * X) + 64 * (X * X * X * X * X) + 16 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-2 * X + 4 * (X * X) + 22 * (X * X * X) + 24 * (X * X * X * X) + 8 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 * X - 8 * (X * X) - 10 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-4 + 8 * X + 156 * X ^ 2 + 368 * X ^ 3 + 320 * X ^ 4 + 96 * X ^ 5) * G + (-4 * X + 4 * X ^ 2 + 52 * X ^ 3 + 92 * X ^ 4 + 64 * X ^ 5 + 16 * X ^ 6) * derivative ℚ G =
      -2 + 8 * X + 66 * X ^ 2 + 96 * X ^ 3 + 40 * X ^ 4 + (-2 - 16 * X - 30 * X ^ 2 - 16 * X ^ 3) * S + (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 14 * X ^ 2 - 36 * X ^ 3 - 39 * X ^ 4 - 20 * X ^ 5 - 4 * X ^ 6) * ((16 - 16 * X - 224 * X ^ 2 - 320 * X ^ 3 - 128 * X ^ 4) * derivative ℚ G + (-48 - 96 * X - 192 * X ^ 2 - 128 * X ^ 3) * G - (-32))) = 0 := by
    linear_combination (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) ^ 2 * S * hdS - 2 * (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 - 16 * X - 30 * X ^ 2 - 16 * X ^ 3) * (1 - 4 * X - 4 * X ^ 2) + (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) * (-4 - 8 * X)) * hk + 2 * (-2 * X - 8 * X ^ 2 - 10 * X ^ 3 - 4 * X ^ 4) * (1 - 4 * X - 4 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 14 * X ^ 2 - 36 * X ^ 3 - 39 * X ^ 4 - 20 * X ^ 5 - 4 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2)
    (hG : G * (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 + (1 + X) * S) = 3 * X + 2 * X ^ 2 + (-X) * S) :
    (X ^ 2 - 3 * X ^ 3 - 8 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-4 * X ^ 2 - 26 * X ^ 3 - 20 * X ^ 4) * derivative ℚ G + (-6 * X ^ 2 - 12 * X ^ 3) * G =
      0 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d224 : derivative ℚ (224 : ℚ⟦X⟧) = 0 := dnum 224
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have hL : derivative ℚ ((16 - 16 * X - 224 * (X * X) - 320 * (X * X * X) - 128 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-48 - 96 * X - 192 * (X * X) - 128 * (X * X * X) : ℚ⟦X⟧) * G) =
      (-16 - 448 * X - 960 * X ^ 2 - 512 * X ^ 3) * derivative ℚ G + (16 - 16 * X - 224 * X ^ 2 - 320 * X ^ 3 - 128 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-96 - 384 * X - 384 * X ^ 2) * G + (-48 - 96 * X - 192 * X ^ 2 - 128 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d48, d96, d128, d192, d224, d320]
    ring
  have hRd : derivative ℚ (-32 : ℚ⟦X⟧) = 0 := by
    simp [d32]
  have h2 : (16 - 16 * X - 224 * (X * X) - 320 * (X * X * X) - 128 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-48 - 96 * X - 192 * (X * X) - 128 * (X * X * X) : ℚ⟦X⟧) * G = (-32 : ℚ⟦X⟧) := by linear_combination h
  have hd : (-16 - 448 * X - 960 * X ^ 2 - 512 * X ^ 3) * derivative ℚ G + (16 - 16 * X - 224 * X ^ 2 - 320 * X ^ 3 - 128 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-96 - 384 * X - 384 * X ^ 2) * G + (-48 - 96 * X - 192 * X ^ 2 - 128 * X ^ 3) * derivative ℚ G = 0 := by
    rw [← hL, h2, hRd]
  have hfull : (16 + 32 * X) * ((X ^ 2 - 3 * X ^ 3 - 8 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-4 * X ^ 2 - 26 * X ^ 3 - 20 * X ^ 4) * derivative ℚ G + (-6 * X ^ 2 - 12 * X ^ 3) * G - (0)) = 0 := by
    linear_combination (X ^ 2) * hd + (0) * h
  have hg : (16 + 32 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2)
    (hG : G * (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 + (1 + X) * S) = 3 * X + 2 * X ^ 2 + (-X) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-3) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-8) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-4) +
      derivative ℚ G * X * X * C (-4) + derivative ℚ G * X * X * X * C (-26) +
      derivative ℚ G * X * X * X * X * C (-20) + G * X * X * C (-6) +
      G * X * X * X * C (-12) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2)
    (hG : G * (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 + (1 + X) * S) = 3 * X + 2 * X ^ 2 + (-X) * S) (m : ℕ) :
    1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-8) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-4) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-26) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-20) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-6) * coeff (m + 1 + 1 + 1) G +
      (-12) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2)
    (hG : G * (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 + (1 + X) * S) = 3 * X + 2 * X ^ 2 + (-X) * S) :
    6 * coeff (0 + 1 + 1 + 1) G + (-6) * coeff (0 + 1 + 1) G +
      (-8) * coeff (0 + 1 + 1) G + (-26) * coeff (0 + 1) G +
      (-6) * coeff (0 + 1) G + (-12) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2)
    (hG : G * (-1 + 3 * X + 8 * X ^ 2 + 4 * X ^ 3 + (1 + X) * S) = 3 * X + 2 * X ^ 2 + (-X) * S) :
    12 * coeff (0 + 1 + 1 + 1 + 1) G + (-18) * coeff (0 + 1 + 1 + 1) G +
      (-16) * coeff (0 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1) G +
      (-52) * coeff (0 + 1 + 1) G + (-20) * coeff (0 + 1) G +
      (-6) * coeff (0 + 1 + 1) G + (-12) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A240688Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a240688.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A240688Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A240688Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A240688Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
