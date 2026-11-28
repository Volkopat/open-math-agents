import OMAStatements.S_oeis_a242781

-- Problem: A242781: Expansion of (1 - 2*x - sqrt(1-4*x))/(4*x^2 + sqrt(1-4*x)*(3*x+1) - 5*x + 1).
-- Upstream: formal-conjectures statements/oeis-a242781.lean:0 (declaration OMA.S_oeis_a242781.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A242781Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 5 * X + 4 * X ^ 2 + (1 + 3 * X) * S) = 1 - 2 * X + (-1) * S) :
    (48 * X - 288 * X ^ 2 + 352 * X ^ 3 + 96 * X ^ 4 + 112 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G + (48 - 288 * X + 288 * X ^ 2 - 384 * X ^ 3 + 304 * X ^ 4 + 96 * X ^ 5) * G = 144 * X ^ 2 - 96 * X ^ 3 - 16 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-12 * X + 48 * X ^ 2 - 4 * X ^ 3 + 16 * X ^ 4) * G = (2 - 8 * X + 2 * X ^ 2 - 8 * X ^ 3 : ℚ⟦X⟧) + (-2 + 4 * X + 2 * X ^ 2) * S := by
    linear_combination (1 - 5 * X + 4 * X ^ 2 - (1 + 3 * X) * S) * hG + (1 + 3 * X) * ((1 + 3 * X) * G - (-1)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-12 * X + 48 * (X * X) - 4 * (X * X * X) + 16 * (X * X * X * X) : ℚ⟦X⟧) * G) = (-12 + 96 * X - 12 * X ^ 2 + 64 * X ^ 3) * G + (-12 * X + 48 * X ^ 2 - 4 * X ^ 3 + 16 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d12, d16, d48]
    ring
  have hR : derivative ℚ ((2 - 8 * X + 2 * (X * X) - 8 * (X * X * X) : ℚ⟦X⟧) + (-2 + 4 * X + 2 * (X * X) : ℚ⟦X⟧) * S) =
      -8 + 4 * X - 24 * X ^ 2 + (4 + 4 * X) * S + (-2 + 4 * X + 2 * X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d8]
    ring
  have hk2 : (-12 * X + 48 * (X * X) - 4 * (X * X * X) + 16 * (X * X * X * X) : ℚ⟦X⟧) * G = (2 - 8 * X + 2 * (X * X) - 8 * (X * X * X) : ℚ⟦X⟧) + (-2 + 4 * X + 2 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-12 + 96 * X - 12 * X ^ 2 + 64 * X ^ 3) * G + (-12 * X + 48 * X ^ 2 - 4 * X ^ 3 + 16 * X ^ 4) * derivative ℚ G =
      -8 + 4 * X - 24 * X ^ 2 + (4 + 4 * X) * S + (-2 + 4 * X + 2 * X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 4 * X) * ((48 * X - 288 * X ^ 2 + 352 * X ^ 3 + 96 * X ^ 4 + 112 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G + (48 - 288 * X + 288 * X ^ 2 - 384 * X ^ 3 + 304 * X ^ 4 + 96 * X ^ 5) * G - (144 * X ^ 2 - 96 * X ^ 3 - 16 * X ^ 4)) = 0 := by
    linear_combination (-2 + 4 * X + 2 * X ^ 2) ^ 2 * S * hdS - 2 * (-2 + 4 * X + 2 * X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (4 + 4 * X) * (1 - 4 * X) + (-2 + 4 * X + 2 * X ^ 2) * (-4)) * hk + 2 * (-2 + 4 * X + 2 * X ^ 2) * (1 - 4 * X) * hdk
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 5 * X + 4 * X ^ 2 + (1 + 3 * X) * S) = 1 - 2 * X + (-1) * S) :
    derivative ℚ G * X * C 48 + derivative ℚ G * X * X * C (-288) +
      derivative ℚ G * X * X * X * C 352 + derivative ℚ G * X * X * X * X * C 96 +
      derivative ℚ G * X * X * X * X * X * C 112 + derivative ℚ G * X * X * X * X * X * X * C 64 +
      G * C 48 + G * X * C (-288) +
      G * X * X * C 288 + G * X * X * X * C (-384) +
      G * X * X * X * X * C 304 + G * X * X * X * X * X * C 96 =
      C 144 * X * X + C (-96) * X * X * X +
      C (-16) * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 5 * X + 4 * X ^ 2 + (1 + 3 * X) * S) = 1 - 2 * X + (-1) * S) (m : ℕ) :
    48 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-288) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      352 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 96 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      112 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 64 * ((m : ℚ) + 1) * coeff (m + 1) G +
      48 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-288) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      288 * coeff (m + 1 + 1 + 1 + 1) G + (-384) * coeff (m + 1 + 1 + 1) G +
      304 * coeff (m + 1 + 1) G + 96 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 5 * X + 4 * X ^ 2 + (1 + 3 * X) * S) = 1 - 2 * X + (-1) * S) :
    240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1152) * coeff (0 + 1 + 1 + 1 + 1) G +
      1056 * coeff (0 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1) G +
      112 * coeff (0 + 1) G + 48 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-288) * coeff (0 + 1 + 1 + 1 + 1) G + 288 * coeff (0 + 1 + 1 + 1) G +
      (-384) * coeff (0 + 1 + 1) G + 304 * coeff (0 + 1) G +
      96 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A242781Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a242781.main := by
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
    have r := A242781Aux.relE0 (S) G (by linear_combination hS)
      (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A242781Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
