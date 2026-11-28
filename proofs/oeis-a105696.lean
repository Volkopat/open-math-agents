import OMAStatements.S_oeis_a105696

-- Problem: A105696: Expansion of (1-x)/sqrt((1-3*x)/(1+x)).
-- Upstream: formal-conjectures statements/oeis-a105696.lean:0 (declaration OMA.S_oeis_a105696.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Differentiating F^2 (1-3x) = (1-x)^2 (1+x), multiplying by F (1-3x) and cancelling 2 (1-x)
gives the differential equation (1-x)(1+x)(1-3x) F' = (1+3x^2) F. The recurrence is the
coefficient of x^(n-1) in this equation. -/

namespace A105696Aux

open PowerSeries

theorem c_succ (f : ℚ⟦X⟧) (c : ℚ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℚ⟦X⟧) (c : ℚ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem ode (F : ℚ⟦X⟧) (hF : F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X)) :
    derivative ℚ F * (1 - C 1 * X) * (1 - C (-1) * X) * (1 - C 3 * X) =
      F + F * X * X * C 3 := by
  have h1c : (C 1 : ℚ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℚ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have h3 : (C 3 : ℚ⟦X⟧) = 3 := map_ofNat C 3
  have hF' : F * F * (1 - C 3 * X) = (1 - X) * (1 - X) * (1 + X) := by
    rw [h3]
    linear_combination hF
  have hd := congrArg (derivative ℚ) hF'
  simp [Derivation.leibniz] at hd
  rw [h3] at hd
  have hmul : (1 - X) * (2 * (derivative ℚ F * (1 - X) * (1 + X) * (1 - 3 * X) -
      F * (1 + 3 * X ^ 2))) = 0 := by
    linear_combination F * (1 - 3 * X) * hd + (3 * F - 2 * (1 - 3 * X) * derivative ℚ F) * hF
  have h1 : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2T := (mul_eq_zero.mp hmul).resolve_left h1
  have hC : C 2 * (derivative ℚ F * (1 - C 1 * X) * (1 - C (-1) * X) * (1 - C 3 * X) -
      (F + F * X * X * C 3)) = 0 := by
    rw [h1c, hm1, h2, h3]
    linear_combination h2T
  ext n
  have h := congrArg (coeff n) hC
  rw [coeff_C_mul, map_sub, map_zero] at h
  linarith

theorem relA (F : ℚ⟦X⟧) (hF : F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X)) :
    3 * coeff (0 + 1 + 1 + 1) F - 7 * coeff (0 + 1 + 1) F - coeff (0 + 1) F -
      3 * coeff 0 F = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (ode F hF)
  simp only [c_succ, c_zero, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
    coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem relB (F : ℚ⟦X⟧) (hF : F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X)) (m : ℕ) :
    ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) F +
      (-3 * ((m : ℚ) + 4) + 2) * coeff (m + 1 + 1 + 1) F +
      (-((m : ℚ) + 4) + 2) * coeff (m + 1 + 1) F + 3 * (m : ℚ) * coeff (m + 1) F = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (ode F hF)
  simp only [c_succ, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
    coeff_derivative] at h
  push_cast at h
  linear_combination h

end A105696Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a105696.main := by
  intro F hF _ n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : j + 1 + 1 + 1 - 1 = j + 1 + 1 := rfl
  have e2 : j + 1 + 1 + 1 - 2 = j + 1 := rfl
  have e3 : j + 1 + 1 + 1 - 3 = j := rfl
  rw [e1, e2, e3]
  cases j with
  | zero =>
    have r := A105696Aux.relA F hF
    push_cast
    linear_combination r
  | succ m =>
    have r := A105696Aux.relB F hF m
    push_cast
    linear_combination r
