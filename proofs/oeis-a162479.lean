import OMAStatements.S_oeis_a162479

-- Problem: A162479: Expansion of 1/((1-x)*sqrt(1-4x/(1-x)^4)).
-- Upstream: formal-conjectures statements/oeis-a162479.lean:0 (declaration OMA.S_oeis_a162479.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation for G with polynomial coefficients. The recurrence is the
coefficient of a power of x in this equation, beyond the degree of its right side. -/

namespace A162479Aux

open PowerSeries

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X + (0) * S) :
    (2 - 18 * X + 28 * X ^ 2 - 20 * X ^ 3 + 10 * X ^ 4 - 2 * X ^ 5) * derivative ℚ G + (-6 + 4 * X - 12 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4) * G = 0 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hS2 : S * S = (1 - 8 * X + 6 * (X * X) - 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 8 * X - 6 * X ^ 2 + 4 * X ^ 3 - X ^ 4) * G = (0 : ℚ⟦X⟧) + (-1 + X) * S := by
    linear_combination (0 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 8 * X + 6 * (X * X) - 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -8 + 12 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d4, d6, d8]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 + 12 * X - 12 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 8 * X - 6 * (X * X) + 4 * (X * X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G) = (8 - 12 * X + 12 * X ^ 2 - 4 * X ^ 3) * G + (-1 + 8 * X - 6 * X ^ 2 + 4 * X ^ 3 - X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d6, d8]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * S) =
      0 + (1) * S + (-1 + X) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (-1 + 8 * X - 6 * (X * X) + 4 * (X * X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (8 - 12 * X + 12 * X ^ 2 - 4 * X ^ 3) * G + (-1 + 8 * X - 6 * X ^ 2 + 4 * X ^ 3 - X ^ 4) * derivative ℚ G =
      0 + (1) * S + (-1 + X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * ((2 - 18 * X + 28 * X ^ 2 - 20 * X ^ 3 + 10 * X ^ 4 - 2 * X ^ 5) * derivative ℚ G + (-6 + 4 * X - 12 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4) * G - (0)) = 0 := by
    linear_combination (-1 + X) ^ 2 * S * hdS - 2 * (-1 + X) ^ 2 * derivative ℚ S * hS -
      (2 * (1) * (1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4) + (-1 + X) * (-8 + 12 * X - 12 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-1 + X) * (1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * hdk
  have hg : (1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X + (0) * S) :
    derivative ℚ G * C 2 + derivative ℚ G * X * C (-18) +
      derivative ℚ G * X * X * C 28 + derivative ℚ G * X * X * X * C (-20) +
      derivative ℚ G * X * X * X * X * C 10 + derivative ℚ G * X * X * X * X * X * C (-2) +
      G * C (-6) + G * X * C 4 +
      G * X * X * C (-12) + G * X * X * X * C 8 +
      G * X * X * X * X * C (-2) =
      0 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X + (0) * S) (m : ℕ) :
    2 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-18) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      28 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-20) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      10 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-2) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-6) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 4 * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * coeff (m + 1 + 1 + 1) G + 8 * coeff (m + 1 + 1) G +
      (-2) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X + (0) * S) :
    10 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-72) * coeff (0 + 1 + 1 + 1 + 1) G +
      84 * coeff (0 + 1 + 1 + 1) G + (-40) * coeff (0 + 1 + 1) G +
      10 * coeff (0 + 1) G + (-6) * coeff (0 + 1 + 1 + 1 + 1) G +
      4 * coeff (0 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1) G +
      8 * coeff (0 + 1) G + (-2) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A162479Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a162479.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  cases m with
  | zero =>
    have r := A162479Aux.relE0 ((1 - PowerSeries.X) ^ 2 * T) G (by linear_combination hT)
      (by linear_combination (1 - PowerSeries.X) * hG)
    push_cast
    linear_combination ((1 : ℚ) / 2) * r
  | succ m =>
    have r := A162479Aux.rel ((1 - PowerSeries.X) ^ 2 * T) G (by linear_combination hT)
      (by linear_combination (1 - PowerSeries.X) * hG) m
    push_cast
    linear_combination ((1 : ℚ) / 2) * r
