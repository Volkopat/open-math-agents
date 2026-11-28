import OMAStatements.S_oeis_a239201

-- Problem: A239201: Expansion of -(x * sqrt(5*x^2 -6*x +1) -2*x^3 +3*x^2 -x) / ((3*x^2 -4*x +1) * sqrt(5*x^2 -6*x +1) +5*x^3 -11*x^2 +7*x -1).
-- Upstream: formal-conjectures statements/oeis-a239201.lean:0 (declaration OMA.S_oeis_a239201.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A239201Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3 + (1 - 4 * X + 3 * X ^ 2) * S) = X - 3 * X ^ 2 + 2 * X ^ 3 + (-X) * S) :
    (48 * X - 336 * X ^ 2 + 528 * X ^ 3 - 240 * X ^ 4) * derivative ℚ G + (-48 + 192 * X - 144 * X ^ 2) * G = -48 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d22 : derivative ℚ (22 : ℚ⟦X⟧) = 0 := dnum 22
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d72 : derivative ℚ (72 : ℚ⟦X⟧) = 0 := dnum 72
  have hS2 : S * S = (1 - 6 * X + 5 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 2 + 32 * X ^ 3 - 72 * X ^ 4 + 64 * X ^ 5 - 20 * X ^ 6) * G = (-2 * X ^ 3 + 14 * X ^ 4 - 22 * X ^ 5 + 10 * X ^ 6 : ℚ⟦X⟧) + (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) * S := by
    linear_combination (-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3 - (1 - 4 * X + 3 * X ^ 2) * S) * hG + (1 - 4 * X + 3 * X ^ 2) * ((1 - 4 * X + 3 * X ^ 2) * G - (-X)) * hS
  have hPd : derivative ℚ (1 - 6 * X + 5 * (X * X) : ℚ⟦X⟧) = -6 + 10 * X := by
    simp [Derivation.leibniz, d5, d6]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -6 + 10 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X) + 32 * (X * X * X) - 72 * (X * X * X * X) + 64 * (X * X * X * X * X) - 20 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-8 * X + 96 * X ^ 2 - 288 * X ^ 3 + 320 * X ^ 4 - 120 * X ^ 5) * G + (-4 * X ^ 2 + 32 * X ^ 3 - 72 * X ^ 4 + 64 * X ^ 5 - 20 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d20, d32, d64, d72]
    ring
  have hR : derivative ℚ ((-2 * (X * X * X) + 14 * (X * X * X * X) - 22 * (X * X * X * X * X) + 10 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-6 * (X * X * X) + 12 * (X * X * X * X) - 6 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      -6 * X ^ 2 + 56 * X ^ 3 - 110 * X ^ 4 + 60 * X ^ 5 + (-18 * X ^ 2 + 48 * X ^ 3 - 30 * X ^ 4) * S + (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d6, d10, d12, d14, d22]
    ring
  have hk2 : (-4 * (X * X) + 32 * (X * X * X) - 72 * (X * X * X * X) + 64 * (X * X * X * X * X) - 20 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-2 * (X * X * X) + 14 * (X * X * X * X) - 22 * (X * X * X * X * X) + 10 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-6 * (X * X * X) + 12 * (X * X * X * X) - 6 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X + 96 * X ^ 2 - 288 * X ^ 3 + 320 * X ^ 4 - 120 * X ^ 5) * G + (-4 * X ^ 2 + 32 * X ^ 3 - 72 * X ^ 4 + 64 * X ^ 5 - 20 * X ^ 6) * derivative ℚ G =
      -6 * X ^ 2 + 56 * X ^ 3 - 110 * X ^ 4 + 60 * X ^ 5 + (-18 * X ^ 2 + 48 * X ^ 3 - 30 * X ^ 4) * S + (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 4 * ((1 - 9 * X + 26 * X ^ 2 - 34 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5) * ((48 * X - 336 * X ^ 2 + 528 * X ^ 3 - 240 * X ^ 4) * derivative ℚ G + (-48 + 192 * X - 144 * X ^ 2) * G - (-48 * X ^ 2))) = 0 := by
    linear_combination (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) ^ 2 * S * hdS - 2 * (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-18 * X ^ 2 + 48 * X ^ 3 - 30 * X ^ 4) * (1 - 6 * X + 5 * X ^ 2) + (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) * (-6 + 10 * X)) * hk + 2 * (-6 * X ^ 3 + 12 * X ^ 4 - 6 * X ^ 5) * (1 - 6 * X + 5 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 4 ≠ 0 := pow_ne_zero 4 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 9 * X + 26 * X ^ 2 - 34 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3 + (1 - 4 * X + 3 * X ^ 2) * S) = X - 3 * X ^ 2 + 2 * X ^ 3 + (-X) * S) :
    derivative ℚ G * X * C 48 + derivative ℚ G * X * X * C (-336) +
      derivative ℚ G * X * X * X * C 528 + derivative ℚ G * X * X * X * X * C (-240) +
      G * C (-48) + G * X * C 192 +
      G * X * X * C (-144) =
      C (-48) * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3 + (1 - 4 * X + 3 * X ^ 2) * S) = X - 3 * X ^ 2 + 2 * X ^ 3 + (-X) * S) (m : ℕ) :
    48 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-336) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      528 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-240) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-48) * coeff (m + 1 + 1 + 1 + 1) G + 192 * coeff (m + 1 + 1 + 1) G +
      (-144) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hG : G * (-1 + 7 * X - 11 * X ^ 2 + 5 * X ^ 3 + (1 - 4 * X + 3 * X ^ 2) * S) = X - 3 * X ^ 2 + 2 * X ^ 3 + (-X) * S) :
    144 * coeff (0 + 1 + 1 + 1) G + (-672) * coeff (0 + 1 + 1) G +
      528 * coeff (0 + 1) G + (-48) * coeff (0 + 1 + 1 + 1) G +
      192 * coeff (0 + 1 + 1) G + (-144) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A239201Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a239201.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A239201Aux.relE0 (S) G (by linear_combination hS)
      (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 48) * r
  | succ m =>
    have r := A239201Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 48) * r
