import OMAStatements.S_oeis_a247170

-- Problem: A247170: Expansion of (-3/2+(x^3+3*x)/(sqrt(x^4-4*x^3-2*x^2+1)*2*x)).
-- Upstream: formal-conjectures statements/oeis-a247170.lean:0 (declaration OMA.S_oeis_a247170.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A247170Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X) * S) = 3 * X + X ^ 3 + (-3 * X) * S) :
    (48 - 80 * X ^ 2 - 192 * X ^ 3 + 16 * X ^ 4 - 64 * X ^ 5 + 16 * X ^ 6) * derivative ℚ G + (-128 * X - 288 * X ^ 2 + 128 * X ^ 3 + 32 * X ^ 4) * G = 192 * X + 432 * X ^ 2 - 192 * X ^ 3 - 48 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hS2 : S * S = (1 - 2 * (X * X) - 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 2 + 8 * X ^ 4 + 16 * X ^ 5 - 4 * X ^ 6) * G = (6 * X ^ 2 - 12 * X ^ 4 - 24 * X ^ 5 + 6 * X ^ 6 : ℚ⟦X⟧) + (-6 * X ^ 2 - 2 * X ^ 4) * S := by
    linear_combination (0 - (2 * X) * S) * hG + (2 * X) * ((2 * X) * G - (-3 * X)) * hS
  have hPd : derivative ℚ (1 - 2 * (X * X) - 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -4 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 * X - 12 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X) + 8 * (X * X * X * X) + 16 * (X * X * X * X * X) - 4 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-8 * X + 32 * X ^ 3 + 80 * X ^ 4 - 24 * X ^ 5) * G + (-4 * X ^ 2 + 8 * X ^ 4 + 16 * X ^ 5 - 4 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d16]
    ring
  have hR : derivative ℚ ((6 * (X * X) - 12 * (X * X * X * X) - 24 * (X * X * X * X * X) + 6 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-6 * (X * X) - 2 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      12 * X - 48 * X ^ 3 - 120 * X ^ 4 + 36 * X ^ 5 + (-12 * X - 8 * X ^ 3) * S + (-6 * X ^ 2 - 2 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d6, d12, d24]
    ring
  have hk2 : (-4 * (X * X) + 8 * (X * X * X * X) + 16 * (X * X * X * X * X) - 4 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (6 * (X * X) - 12 * (X * X * X * X) - 24 * (X * X * X * X * X) + 6 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-6 * (X * X) - 2 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X + 32 * X ^ 3 + 80 * X ^ 4 - 24 * X ^ 5) * G + (-4 * X ^ 2 + 8 * X ^ 4 + 16 * X ^ 5 - 4 * X ^ 6) * derivative ℚ G =
      12 * X - 48 * X ^ 3 - 120 * X ^ 4 + 36 * X ^ 5 + (-12 * X - 8 * X ^ 3) * S + (-6 * X ^ 2 - 2 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 4 * ((1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * ((48 - 80 * X ^ 2 - 192 * X ^ 3 + 16 * X ^ 4 - 64 * X ^ 5 + 16 * X ^ 6) * derivative ℚ G + (-128 * X - 288 * X ^ 2 + 128 * X ^ 3 + 32 * X ^ 4) * G - (192 * X + 432 * X ^ 2 - 192 * X ^ 3 - 48 * X ^ 4))) = 0 := by
    linear_combination (-6 * X ^ 2 - 2 * X ^ 4) ^ 2 * S * hdS - 2 * (-6 * X ^ 2 - 2 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-12 * X - 8 * X ^ 3) * (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) + (-6 * X ^ 2 - 2 * X ^ 4) * (-4 * X - 12 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-6 * X ^ 2 - 2 * X ^ 4) * (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 4 ≠ 0 := pow_ne_zero 4 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X) * S) = 3 * X + X ^ 3 + (-3 * X) * S) :
    (2 * X ^ 2 + 2 * X ^ 3 - 4 * X ^ 4 - 12 * X ^ 5 - 6 * X ^ 6 + 2 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-5 * X - 5 * X ^ 2 - 2 * X ^ 3 - 18 * X ^ 4 - 9 * X ^ 5 + 7 * X ^ 6) * derivative ℚ G + (8 * X ^ 2 + 14 * X ^ 3 + 6 * X ^ 4) * G =
      -12 * X ^ 2 - 21 * X ^ 3 - 9 * X ^ 4 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d288 : derivative ℚ (288 : ℚ⟦X⟧) = 0 := dnum 288
  have d432 : derivative ℚ (432 : ℚ⟦X⟧) = 0 := dnum 432
  have hL : derivative ℚ ((48 - 80 * (X * X) - 192 * (X * X * X) + 16 * (X * X * X * X) - 64 * (X * X * X * X * X) + 16 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-128 * X - 288 * (X * X) + 128 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (-160 * X - 576 * X ^ 2 + 64 * X ^ 3 - 320 * X ^ 4 + 96 * X ^ 5) * derivative ℚ G + (48 - 80 * X ^ 2 - 192 * X ^ 3 + 16 * X ^ 4 - 64 * X ^ 5 + 16 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-128 - 576 * X + 384 * X ^ 2 + 128 * X ^ 3) * G + (-128 * X - 288 * X ^ 2 + 128 * X ^ 3 + 32 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d32, d48, d64, d80, d128, d192, d288]
    ring
  have hRd : derivative ℚ (192 * X + 432 * (X * X) - 192 * (X * X * X) - 48 * (X * X * X * X) : ℚ⟦X⟧) = 192 + 864 * X - 576 * X ^ 2 - 192 * X ^ 3 := by
    simp [Derivation.leibniz, d48, d192, d432]
    ring
  have h2 : (48 - 80 * (X * X) - 192 * (X * X * X) + 16 * (X * X * X * X) - 64 * (X * X * X * X * X) + 16 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-128 * X - 288 * (X * X) + 128 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) * G = (192 * X + 432 * (X * X) - 192 * (X * X * X) - 48 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-160 * X - 576 * X ^ 2 + 64 * X ^ 3 - 320 * X ^ 4 + 96 * X ^ 5) * derivative ℚ G + (48 - 80 * X ^ 2 - 192 * X ^ 3 + 16 * X ^ 4 - 64 * X ^ 5 + 16 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-128 - 576 * X + 384 * X ^ 2 + 128 * X ^ 3) * G + (-128 * X - 288 * X ^ 2 + 128 * X ^ 3 + 32 * X ^ 4) * derivative ℚ G = 192 + 864 * X - 576 * X ^ 2 - 192 * X ^ 3 := by
    rw [← hL, h2, hRd]
  have hfull : (48 + 16 * X ^ 2) * ((2 * X ^ 2 + 2 * X ^ 3 - 4 * X ^ 4 - 12 * X ^ 5 - 6 * X ^ 6 + 2 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-5 * X - 5 * X ^ 2 - 2 * X ^ 3 - 18 * X ^ 4 - 9 * X ^ 5 + 7 * X ^ 6) * derivative ℚ G + (8 * X ^ 2 + 14 * X ^ 3 + 6 * X ^ 4) * G - (-12 * X ^ 2 - 21 * X ^ 3 - 9 * X ^ 4)) = 0 := by
    linear_combination (2 * X ^ 2 + 2 * X ^ 3) * hd + (-5 * X - 5 * X ^ 2) * h
  have hg : (48 + 16 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (48 : ℚ⟦X⟧) = 48 := cnum 48
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X) * S) = 3 * X + X ^ 3 + (-3 * X) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 2 + derivative ℚ (derivative ℚ G) * X * X * X * C 2 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-4) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-12) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-6) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 2 +
      derivative ℚ G * X * C (-5) + derivative ℚ G * X * X * C (-5) +
      derivative ℚ G * X * X * X * C (-2) + derivative ℚ G * X * X * X * X * C (-18) +
      derivative ℚ G * X * X * X * X * X * C (-9) + derivative ℚ G * X * X * X * X * X * X * C 7 +
      G * X * X * C 8 + G * X * X * X * C 14 +
      G * X * X * X * X * C 6 =
      C (-12) * X * X + C (-21) * X * X * X +
      C (-9) * X * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X) * S) = 3 * X + X ^ 3 + (-3 * X) * S) (m : ℕ) :
    2 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-12) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-6) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 2 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-5) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-2) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-18) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-9) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 7 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      8 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 14 * coeff (m + 1 + 1 + 1 + 1) G +
      6 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X) * S) = 3 * X + X ^ 3 + (-3 * X) * S) :
    40 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-24) * coeff (0 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1) G +
      (-25) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-20) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-6) * coeff (0 + 1 + 1 + 1) G + (-36) * coeff (0 + 1 + 1) G +
      (-9) * coeff (0 + 1) G + 8 * coeff (0 + 1 + 1 + 1) G +
      14 * coeff (0 + 1 + 1) G + 6 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (2 * X) * S) = 3 * X + X ^ 3 + (-3 * X) * S) :
    60 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 40 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1 + 1 + 1) G + (-72) * coeff (0 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1 + 1) G + (-30) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-25) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-54) * coeff (0 + 1 + 1 + 1) G + (-18) * coeff (0 + 1 + 1) G +
      7 * coeff (0 + 1) G + 8 * coeff (0 + 1 + 1 + 1 + 1) G +
      14 * coeff (0 + 1 + 1 + 1) G + 6 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A247170Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a247170.main := by
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
    have r := A247170Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A247170Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A247170Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
