import OMAStatements.S_oeis_a234269

-- Problem: A234269: Expansion of (1-2*x^2-sqrt(1-4*x^2-4*x^3))/(2*x*sqrt(1-4*x^2-4*x^3)).
-- Upstream: formal-conjectures statements/oeis-a234269.lean:0 (declaration OMA.S_oeis_a234269.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A234269Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (0 + (2 * X) * S) = 1 - 2 * X ^ 2 + (-1) * S) :
    (16 * X - 96 * X ^ 3 - 64 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ G + (16 - 96 * X ^ 2 - 160 * X ^ 3 + 64 * X ^ 5) * G = 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 4 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 2 + 16 * X ^ 4 + 16 * X ^ 5) * G = (2 * X - 8 * X ^ 3 - 8 * X ^ 4 : ℚ⟦X⟧) + (-2 * X + 4 * X ^ 3) * S := by
    linear_combination (0 - (2 * X) * S) * hG + (2 * X) * ((2 * X) * G - (-1)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) = -8 * X - 12 * X ^ 2 := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X - 12 * X ^ 2 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X) + 16 * (X * X * X * X) + 16 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (-8 * X + 64 * X ^ 3 + 80 * X ^ 4) * G + (-4 * X ^ 2 + 16 * X ^ 4 + 16 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d16]
    ring
  have hR : derivative ℚ ((2 * X - 8 * (X * X * X) - 8 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 4 * (X * X * X) : ℚ⟦X⟧) * S) =
      2 - 24 * X ^ 2 - 32 * X ^ 3 + (-2 + 12 * X ^ 2) * S + (-2 * X + 4 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hk2 : (-4 * (X * X) + 16 * (X * X * X * X) + 16 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * X - 8 * (X * X * X) - 8 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 4 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X + 64 * X ^ 3 + 80 * X ^ 4) * G + (-4 * X ^ 2 + 16 * X ^ 4 + 16 * X ^ 5) * derivative ℚ G =
      2 - 24 * X ^ 2 - 32 * X ^ 3 + (-2 + 12 * X ^ 2) * S + (-2 * X + 4 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 4 * X ^ 2 - 4 * X ^ 3) * ((16 * X - 96 * X ^ 3 - 64 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ G + (16 - 96 * X ^ 2 - 160 * X ^ 3 + 64 * X ^ 5) * G - (48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4))) = 0 := by
    linear_combination (-2 * X + 4 * X ^ 3) ^ 2 * S * hdS - 2 * (-2 * X + 4 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 + 12 * X ^ 2) * (1 - 4 * X ^ 2 - 4 * X ^ 3) + (-2 * X + 4 * X ^ 3) * (-8 * X - 12 * X ^ 2)) * hk + 2 * (-2 * X + 4 * X ^ 3) * (1 - 4 * X ^ 2 - 4 * X ^ 3) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (0 + (2 * X) * S) = 1 - 2 * X ^ 2 + (-1) * S) :
    (-2 * X ^ 2 - 2 * X ^ 3 + 8 * X ^ 4 + 16 * X ^ 5 + 8 * X ^ 6) * derivative ℚ (derivative ℚ G) + (X + 2 * X ^ 2 + 20 * X ^ 3 + 48 * X ^ 4 + 28 * X ^ 5) * derivative ℚ G + (5 + 6 * X + 4 * X ^ 2 + 10 * X ^ 3 + 8 * X ^ 4) * G =
      3 * X ^ 2 + 2 * X ^ 3 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have hL : derivative ℚ ((16 * X - 96 * (X * X * X) - 64 * (X * X * X * X) + 128 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 96 * (X * X) - 160 * (X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (16 - 288 * X ^ 2 - 256 * X ^ 3 + 640 * X ^ 4 + 768 * X ^ 5) * derivative ℚ G + (16 * X - 96 * X ^ 3 - 64 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-192 * X - 480 * X ^ 2 + 320 * X ^ 4) * G + (16 - 96 * X ^ 2 - 160 * X ^ 3 + 64 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d64, d96, d128, d160]
    ring
  have hRd : derivative ℚ (48 * (X * X) + 64 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) = 96 * X + 192 * X ^ 2 + 128 * X ^ 3 := by
    simp [Derivation.leibniz, d32, d48, d64]
    ring
  have h2 : (16 * X - 96 * (X * X * X) - 64 * (X * X * X * X) + 128 * (X * X * X * X * X) + 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 - 96 * (X * X) - 160 * (X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (48 * (X * X) + 64 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (16 - 288 * X ^ 2 - 256 * X ^ 3 + 640 * X ^ 4 + 768 * X ^ 5) * derivative ℚ G + (16 * X - 96 * X ^ 3 - 64 * X ^ 4 + 128 * X ^ 5 + 128 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-192 * X - 480 * X ^ 2 + 320 * X ^ 4) * G + (16 - 96 * X ^ 2 - 160 * X ^ 3 + 64 * X ^ 5) * derivative ℚ G = 96 * X + 192 * X ^ 2 + 128 * X ^ 3 := by
    rw [← hL, h2, hRd]
  have hfull : (16 - 32 * X ^ 2) * ((-2 * X ^ 2 - 2 * X ^ 3 + 8 * X ^ 4 + 16 * X ^ 5 + 8 * X ^ 6) * derivative ℚ (derivative ℚ G) + (X + 2 * X ^ 2 + 20 * X ^ 3 + 48 * X ^ 4 + 28 * X ^ 5) * derivative ℚ G + (5 + 6 * X + 4 * X ^ 2 + 10 * X ^ 3 + 8 * X ^ 4) * G - (3 * X ^ 2 + 2 * X ^ 3)) = 0 := by
    linear_combination (-2 * X - 2 * X ^ 2) * hd + (5 + 6 * X) * h
  have hg : (16 - 32 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (0 + (2 * X) * S) = 1 - 2 * X ^ 2 + (-1) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C (-2) + derivative ℚ (derivative ℚ G) * X * X * X * C (-2) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 8 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 16 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 8 + derivative ℚ G * X * C 1 +
      derivative ℚ G * X * X * C 2 + derivative ℚ G * X * X * X * C 20 +
      derivative ℚ G * X * X * X * X * C 48 + derivative ℚ G * X * X * X * X * X * C 28 +
      G * C 5 + G * X * C 6 +
      G * X * X * C 4 + G * X * X * X * C 10 +
      G * X * X * X * X * C 8 =
      C 3 * X * X + C 2 * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (0 + (2 * X) * S) = 1 - 2 * X ^ 2 + (-1) * S) (m : ℕ) :
    (-2) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      8 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      8 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 1 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 20 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      48 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 28 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      5 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 6 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1) G + 10 * coeff (m + 1 + 1 + 1) G +
      8 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (0 + (2 * X) * S) = 1 - 2 * X ^ 2 + (-1) * S) :
    (-24) * coeff (0 + 1 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1) G +
      16 * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1) G + 40 * coeff (0 + 1 + 1) G +
      48 * coeff (0 + 1) G + 5 * coeff (0 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1) G +
      10 * coeff (0 + 1) G + 8 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 - 4 * X ^ 3)
    (hG : G * (0 + (2 * X) * S) = 1 - 2 * X ^ 2 + (-1) * S) :
    (-40) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1 + 1) G + 32 * coeff (0 + 1 + 1) G +
      5 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 8 * coeff (0 + 1 + 1 + 1 + 1) G +
      60 * coeff (0 + 1 + 1 + 1) G + 96 * coeff (0 + 1 + 1) G +
      28 * coeff (0 + 1) G + 5 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1 + 1) G +
      10 * coeff (0 + 1 + 1) G + 8 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A234269Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a234269.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A234269Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A234269Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A234269Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
