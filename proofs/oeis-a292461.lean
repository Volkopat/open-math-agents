import OMAStatements.S_oeis_a292461

-- Problem: A292461: Expansion of (1 - x - x^2 + sqrt((1 - x - x^2)^2 - 4*x^3))/2 in powers of x.
-- Upstream: formal-conjectures statements/oeis-a292461.lean:0 (declaration OMA.S_oeis_a292461.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With P = (1-x-x^2)^2 - 4x^3 = (1-3x+x^2)(1+x+x^2), differentiating S^2 = P and multiplying
by S gives 2 P S' = P' S. The coefficient of x^(n-1) in this equation is the recurrence for the
coefficients of S, and [x^k] S = 2 [x^k] G for k ≥ 3; the coefficient of x^2 enters with the
factor n - 6. -/

namespace A292461Aux

open PowerSeries

theorem q_succ (f : ℚ⟦X⟧) (u v : ℚ) (m : ℕ) :
    coeff (m + 1 + 1) (f * (1 - C u * X - C v * X * X)) =
      coeff (m + 1 + 1) f - u * coeff (m + 1) f - v * coeff m f := by
  have e : f * (1 - C u * X - C v * X * X) = f - f * C u * X - f * C v * X * X := by ring
  rw [e]
  simp only [map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
  ring

theorem ode (S : ℚ⟦X⟧) (hS : S ^ 2 = (1 - X - X ^ 2) ^ 2 - 4 * X ^ 3) :
    derivative ℚ S * (1 - C 3 * X - C (-1) * X * X) * (1 - C (-1) * X - C (-1) * X * X) =
      S * C (-1) + S * X * C (-1) + S * X * X * C (-3) + S * X * X * X * C 2 := by
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have h3 : (C 3 : ℚ⟦X⟧) = 3 := map_ofNat C 3
  have hm3 : (C (-3) : ℚ⟦X⟧) = -3 := by rw [map_neg, map_ofNat]
  have hS' : S * S = 1 - C 2 * X - X * X - C 2 * (X * X * X) + X * X * X * X := by
    rw [h2]
    linear_combination hS
  have hd := congrArg (derivative ℚ) hS'
  simp [Derivation.leibniz] at hd
  rw [h2] at hd
  have hT : 2 * (derivative ℚ S * (1 - 3 * X + X * X) * (1 + X + X * X) -
      (S * (-1) + S * X * (-1) + S * X * X * (-3) + S * X * X * X * 2)) = 0 := by
    linear_combination S * hd - 2 * derivative ℚ S * hS
  have hC : C 2 * (derivative ℚ S * (1 - C 3 * X - C (-1) * X * X) *
      (1 - C (-1) * X - C (-1) * X * X) -
      (S * C (-1) + S * X * C (-1) + S * X * X * C (-3) + S * X * X * X * C 2)) = 0 := by
    rw [hm1, hm3, h3, h2]
    linear_combination hT
  ext n
  have h := congrArg (coeff n) hC
  rw [coeff_C_mul, map_sub, map_zero] at h
  linarith

theorem hcoef (S G : ℚ⟦X⟧) (hG : 2 * G = 1 - X - X ^ 2 + S) (i : ℕ) :
    coeff (i + 1 + 1 + 1) S = 2 * coeff (i + 1 + 1 + 1) G := by
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have hk : S = G * C 2 + ((C 1 * X + C 1) * X + C (-1)) := by
    rw [h1c, hm1, h2]
    linear_combination (-1 : ℚ⟦X⟧) * hG
  have h := congrArg (coeff (i + 1 + 1 + 1)) hk
  simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    PowerSeries.coeff_mul_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = (1 - X - X ^ 2) ^ 2 - 4 * X ^ 3)
    (hG : 2 * G = 1 - X - X ^ 2 + S) (m : ℕ) :
    ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-2 * (m : ℚ) - 9) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-(m : ℚ) - 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-2 * (m : ℚ) - 3) * coeff (m + 1 + 1 + 1) G + (m : ℚ) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (ode S hS)
  simp only [q_succ, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
    coeff_derivative] at h
  rw [hcoef S G hG (m + 1 + 1 + 1), hcoef S G hG (m + 1 + 1), hcoef S G hG (m + 1),
    hcoef S G hG m] at h
  have hm : (m : ℚ) * coeff (m + 1 + 1) S = (m : ℚ) * (2 * coeff (m + 1 + 1) G) := by
    cases m with
    | zero => simp
    | succ k => rw [hcoef S G hG k]
  push_cast at h
  linear_combination (1 / 2 : ℚ) * h - (1 / 2 : ℚ) * hm

end A292461Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a292461.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  rw [e1, e2, e3, e4]
  have r := A292461Aux.rel S G hS hG m
  push_cast
  linear_combination r
