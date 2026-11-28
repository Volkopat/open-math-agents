import OMAStatements.S_oeis_a116391

-- Problem: A116391: Expansion of 1/((1+x)*(sqrt(1-4*x^2)-x)).
-- Upstream: formal-conjectures statements/oeis-a116391.lean:0 (declaration OMA.S_oeis_a116391.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Multiplying the defining relation by S + x gives S = (1+x)(1-5x^2) G - x. Differentiating
S^2 = 1-4x^2 and multiplying by S gives (1-2x)(1+2x) S' = -4x S, whose coefficient of x^(n-1)
relates [x^n] S and [x^(n-2)] S. Writing these two coefficients through the coefficients of G
gives the recurrence. -/

namespace A116391Aux

open PowerSeries

theorem c_succ (f : ℚ⟦X⟧) (c : ℚ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem q_succ (f : ℚ⟦X⟧) (u v : ℚ) (m : ℕ) :
    coeff (m + 1 + 1) (f * (1 - C u * X - C v * X * X)) =
      coeff (m + 1 + 1) f - u * coeff (m + 1) f - v * coeff m f := by
  have e : f * (1 - C u * X - C v * X * X) = f - f * C u * X - f * C v * X * X := by ring
  rw [e]
  simp only [map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
  ring

theorem odeS (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2) :
    derivative ℚ S * (1 - C 2 * X) * (1 - C (-2) * X) = S * X * C (-4) := by
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have hm2 : (C (-2) : ℚ⟦X⟧) = -2 := by rw [map_neg, map_ofNat]
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have hm4 : (C (-4) : ℚ⟦X⟧) = -4 := by rw [map_neg, map_ofNat]
  have hS' : S * S = 1 - C 4 * (X * X) := by
    rw [h4]
    linear_combination hS
  have hd := congrArg (derivative ℚ) hS'
  simp [Derivation.leibniz] at hd
  rw [h4] at hd
  have hT : 2 * (derivative ℚ S * (1 - 2 * X) * (1 + 2 * X) - S * X * (-4)) = 0 := by
    linear_combination S * hd - 2 * derivative ℚ S * hS
  have hC : C 2 * (derivative ℚ S * (1 - C 2 * X) * (1 - C (-2) * X) - S * X * C (-4)) = 0 := by
    rw [hm2, hm4, h2]
    linear_combination hT
  ext n
  have h := congrArg (coeff n) hC
  rw [coeff_C_mul, map_sub, map_zero] at h
  linarith

theorem hcoef (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * ((1 + X) * (S - X)) = 1) (i : ℕ) :
    coeff (i + 1 + 1 + 1) S = coeff (i + 1 + 1 + 1) G + coeff (i + 1 + 1) G -
      5 * coeff (i + 1) G - 5 * coeff i G := by
  have h0 : (C 0 : ℚ⟦X⟧) = 0 := map_zero C
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h5 : (C 5 : ℚ⟦X⟧) = 5 := map_ofNat C 5
  have hk : S = G * (1 - C (-1) * X) * (1 - C 0 * X - C 5 * X * X) - C 1 * X := by
    rw [h0, h1c, hm1, h5]
    linear_combination -(S + X) * hG + G * (1 + X) * hS
  have h := congrArg (coeff (i + 1 + 1 + 1)) hk
  simp only [map_sub, q_succ, c_succ, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    Nat.add_one_ne_zero, ↓reduceIte] at h
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * ((1 + X) * (S - X)) = 1) (m : ℕ) :
    ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1) G +
      (-9 * (m : ℚ) - 33) * coeff (m + 1 + 1 + 1) G +
      (-9 * (m : ℚ) - 33) * coeff (m + 1 + 1) G +
      20 * ((m : ℚ) + 2) * coeff (m + 1) G + 20 * ((m : ℚ) + 2) * coeff m G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (odeS S hS)
  simp only [c_succ, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
    coeff_derivative] at h
  rw [hcoef S G hS hG (m + 1 + 1), hcoef S G hS hG m] at h
  push_cast at h
  linear_combination h

end A116391Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a116391.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  have r := A116391Aux.rel S G hS hG m
  push_cast
  linear_combination r
