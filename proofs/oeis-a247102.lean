import OMAStatements.S_oeis_a247102

-- Problem: A247102: Expansion of g.f. (6*x+2)/(sqrt(-3*x^2-6*x+1)*(4*x^2+4*x)) - (2*x+1)/(2*x^2+2*x).
-- Upstream: formal-conjectures statements/oeis-a247102.lean:0 (declaration OMA.S_oeis_a247102.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A247102Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X - 3 * X ^ 2)
    (hG : G * (0 + (4 * X + 4 * X ^ 2) * S) = 2 + 6 * X + (-2 - 4 * X) * S) :
    (256 * X - 512 * X ^ 2 - 6144 * X ^ 3 - 7680 * X ^ 4 - 2304 * X ^ 5) * derivative ℚ G + (256 - 1792 * X - 6912 * X ^ 2 - 11520 * X ^ 3 - 4608 * X ^ 4) * G = 512 + 1536 * X + 3840 * X ^ 2 + 2304 * X ^ 3 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d152 : derivative ℚ (152 : ℚ⟦X⟧) = 0 := dnum 152
  have d168 : derivative ℚ (168 : ℚ⟦X⟧) = 0 := dnum 168
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d224 : derivative ℚ (224 : ℚ⟦X⟧) = 0 := dnum 224
  have hS2 : S * S = (1 - 6 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-16 * X ^ 2 + 64 * X ^ 3 + 224 * X ^ 4 + 192 * X ^ 5 + 48 * X ^ 6) * G = (8 * X - 24 * X ^ 2 - 152 * X ^ 3 - 168 * X ^ 4 - 48 * X ^ 5 : ℚ⟦X⟧) + (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) * S := by
    linear_combination (0 - (4 * X + 4 * X ^ 2) * S) * hG + (4 * X + 4 * X ^ 2) * ((4 * X + 4 * X ^ 2) * G - (-2 - 4 * X)) * hS
  have hPd : derivative ℚ (1 - 6 * X - 3 * (X * X) : ℚ⟦X⟧) = -6 - 6 * X := by
    simp [Derivation.leibniz, d3, d6]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -6 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-16 * (X * X) + 64 * (X * X * X) + 224 * (X * X * X * X) + 192 * (X * X * X * X * X) + 48 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-32 * X + 192 * X ^ 2 + 896 * X ^ 3 + 960 * X ^ 4 + 288 * X ^ 5) * G + (-16 * X ^ 2 + 64 * X ^ 3 + 224 * X ^ 4 + 192 * X ^ 5 + 48 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d48, d64, d192, d224]
    ring
  have hR : derivative ℚ ((8 * X - 24 * (X * X) - 152 * (X * X * X) - 168 * (X * X * X * X) - 48 * (X * X * X * X * X) : ℚ⟦X⟧) + (-8 * X - 32 * (X * X) - 24 * (X * X * X) : ℚ⟦X⟧) * S) =
      8 - 48 * X - 456 * X ^ 2 - 672 * X ^ 3 - 240 * X ^ 4 + (-8 - 64 * X - 72 * X ^ 2) * S + (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d8, d24, d32, d48, d152, d168]
    ring
  have hk2 : (-16 * (X * X) + 64 * (X * X * X) + 224 * (X * X * X * X) + 192 * (X * X * X * X * X) + 48 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (8 * X - 24 * (X * X) - 152 * (X * X * X) - 168 * (X * X * X * X) - 48 * (X * X * X * X * X) : ℚ⟦X⟧) + (-8 * X - 32 * (X * X) - 24 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-32 * X + 192 * X ^ 2 + 896 * X ^ 3 + 960 * X ^ 4 + 288 * X ^ 5) * G + (-16 * X ^ 2 + 64 * X ^ 3 + 224 * X ^ 4 + 192 * X ^ 5 + 48 * X ^ 6) * derivative ℚ G =
      8 - 48 * X - 456 * X ^ 2 - 672 * X ^ 3 - 240 * X ^ 4 + (-8 - 64 * X - 72 * X ^ 2) * S + (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 4 * X - 14 * X ^ 2 - 12 * X ^ 3 - 3 * X ^ 4) * ((256 * X - 512 * X ^ 2 - 6144 * X ^ 3 - 7680 * X ^ 4 - 2304 * X ^ 5) * derivative ℚ G + (256 - 1792 * X - 6912 * X ^ 2 - 11520 * X ^ 3 - 4608 * X ^ 4) * G - (512 + 1536 * X + 3840 * X ^ 2 + 2304 * X ^ 3))) = 0 := by
    linear_combination (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) ^ 2 * S * hdS - 2 * (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-8 - 64 * X - 72 * X ^ 2) * (1 - 6 * X - 3 * X ^ 2) + (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) * (-6 - 6 * X)) * hk + 2 * (-8 * X - 32 * X ^ 2 - 24 * X ^ 3) * (1 - 6 * X - 3 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X - 14 * X ^ 2 - 12 * X ^ 3 - 3 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X - 3 * X ^ 2)
    (hG : G * (0 + (4 * X + 4 * X ^ 2) * S) = 2 + 6 * X + (-2 - 4 * X) * S) :
    derivative ℚ G * X * C 256 + derivative ℚ G * X * X * C (-512) +
      derivative ℚ G * X * X * X * C (-6144) + derivative ℚ G * X * X * X * X * C (-7680) +
      derivative ℚ G * X * X * X * X * X * C (-2304) + G * C 256 +
      G * X * C (-1792) + G * X * X * C (-6912) +
      G * X * X * X * C (-11520) + G * X * X * X * X * C (-4608) =
      C 512 + C 1536 * X +
      C 3840 * X * X + C 2304 * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X - 3 * X ^ 2)
    (hG : G * (0 + (4 * X + 4 * X ^ 2) * S) = 2 + 6 * X + (-2 - 4 * X) * S) (m : ℕ) :
    256 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-512) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-6144) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-7680) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-2304) * ((m : ℚ) + 1) * coeff (m + 1) G + 256 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-1792) * coeff (m + 1 + 1 + 1 + 1) G + (-6912) * coeff (m + 1 + 1 + 1) G +
      (-11520) * coeff (m + 1 + 1) G + (-4608) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X - 3 * X ^ 2)
    (hG : G * (0 + (4 * X + 4 * X ^ 2) * S) = 2 + 6 * X + (-2 - 4 * X) * S) :
    1024 * coeff (0 + 1 + 1 + 1 + 1) G + (-1536) * coeff (0 + 1 + 1 + 1) G +
      (-12288) * coeff (0 + 1 + 1) G + (-7680) * coeff (0 + 1) G +
      256 * coeff (0 + 1 + 1 + 1 + 1) G + (-1792) * coeff (0 + 1 + 1 + 1) G +
      (-6912) * coeff (0 + 1 + 1) G + (-11520) * coeff (0 + 1) G +
      (-4608) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A247102Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a247102.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A247102Aux.relE0 (S) G (by linear_combination hS)
      (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 256) * r
  | succ m =>
    have r := A247102Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 256) * r
