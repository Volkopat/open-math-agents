import OMAStatements.S_oeis_a239204

-- Problem: A239204: Expansion of ((x-1)*sqrt(x^2-6*x+1)-x^2-4*x+1)/(8*x^3).
-- Upstream: formal-conjectures statements/oeis-a239204.lean:0 (declaration OMA.S_oeis_a239204.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The series H = (x-1) S = 8x^3 G + x^2 + 4x - 1 satisfies H^2 = (1-x)^2 (1-6x+x^2).
Differentiating, multiplying by H and cancelling 2 (1-x) gives
(1-x)(1-6x+x^2) H' = (-4+10x-2x^2) H. The coefficient of x^(n+2) in this equation, written
through the coefficients of G, is the recurrence. -/

namespace A239204Aux

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

theorem odeH (H : ℚ⟦X⟧) (hH : H * H = (1 - X) * (1 - X) * (1 - 6 * X + X * X)) :
    derivative ℚ H * (1 - C 1 * X) * (1 - C 6 * X - C (-1) * X * X) =
      H * C (-4) + H * X * C 10 + H * X * X * C (-2) := by
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have hm2 : (C (-2) : ℚ⟦X⟧) = -2 := by rw [map_neg, map_ofNat]
  have hm4 : (C (-4) : ℚ⟦X⟧) = -4 := by rw [map_neg, map_ofNat]
  have h6 : (C 6 : ℚ⟦X⟧) = 6 := map_ofNat C 6
  have h10 : (C 10 : ℚ⟦X⟧) = 10 := map_ofNat C 10
  have hH' : H * H = (1 - X) * (1 - X) * (1 - C 6 * X + X * X) := by
    rw [h6]
    exact hH
  have hd := congrArg (derivative ℚ) hH'
  simp [Derivation.leibniz] at hd
  rw [h6] at hd
  have hmul : (1 - X) * (2 * (derivative ℚ H * (1 - X) * (1 - 6 * X + X * X) -
      (H * (-4) + H * X * 10 + H * X * X * (-2)))) = 0 := by
    linear_combination H * hd - 2 * derivative ℚ H * hH
  have h1 : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2T := (mul_eq_zero.mp hmul).resolve_left h1
  have hC : C 2 * (derivative ℚ H * (1 - C 1 * X) * (1 - C 6 * X - C (-1) * X * X) -
      (H * C (-4) + H * X * C 10 + H * X * X * C (-2))) = 0 := by
    rw [h1c, hm1, hm2, hm4, h6, h10, h2]
    linear_combination h2T
  ext n
  have h := congrArg (coeff n) hC
  rw [coeff_C_mul, map_sub, map_zero] at h
  linarith

theorem hcoef (S G : ℚ⟦X⟧) (hG : 8 * X ^ 3 * G = (X - 1) * S - X ^ 2 - 4 * X + 1) (i : ℕ) :
    coeff (i + 1 + 1 + 1) ((X - 1) * S) = 8 * coeff i G := by
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have h8 : (C 8 : ℚ⟦X⟧) = 8 := map_ofNat C 8
  have hk : (X - 1) * S = G * X * X * X * C 8 + ((C 1 * X + C 4) * X + C (-1)) := by
    rw [h1c, hm1, h4, h8]
    linear_combination (-1 : ℚ⟦X⟧) * hG
  have h := congrArg (coeff (i + 1 + 1 + 1)) hk
  simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    PowerSeries.coeff_mul_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  linear_combination h

theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = X ^ 2 - 6 * X + 1)
    (hG : 8 * X ^ 3 * G = (X - 1) * S - X ^ 2 - 4 * X + 1) (m : ℕ) :
    ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1) G + (-7 * (m : ℚ) - 31) * coeff (m + 1 + 1) G +
      (7 * (m : ℚ) + 18) * coeff (m + 1) G + (-(m : ℚ) - 1) * coeff m G = 0 := by
  have hH : (X - 1) * S * ((X - 1) * S) = (1 - X) * (1 - X) * (1 - 6 * X + X * X) := by
    linear_combination (1 - X) ^ 2 * hS
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (odeH _ hH)
  simp only [q_succ, c_succ, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
    coeff_derivative] at h
  rw [hcoef S G hG (m + 1 + 1 + 1), hcoef S G hG (m + 1 + 1), hcoef S G hG (m + 1),
    hcoef S G hG m] at h
  push_cast at h
  linear_combination (1 / 8 : ℚ) * h

end A239204Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a239204.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  have r := A239204Aux.rel S G hS hG m
  push_cast
  linear_combination r
