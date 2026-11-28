import OMAStatements.S_oeis_a131135

-- Problem: A131135: Denominator of (ordinary) expansion of log((x/2-1)/(x-1)).
-- Upstream: formal-conjectures statements/oeis-a131135.lean:0 (declaration OMA.S_oeis_a131135.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a131135 PowerSeries

namespace OMA.LogRatio

noncomputable def geom (r : ℚ) : ℚ⟦X⟧ := mk fun n => r ^ n

theorem geom_mul (r : ℚ) : (1 - C r * X) * geom r = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_one]
  cases n with
  | zero => simp [geom, coeff_zero_X_mul]
  | succ n => simp [geom, coeff_succ_X_mul, pow_succ, mul_comm]

theorem dlog_mul : (derivative (R := ℚ)) (logOf F) * F = derivative (R := ℚ) F := by
  have hc : constantCoeff F = 1 := by simp [F, map_sub, constantCoeff_inv]
  have hG : HasSubst (F - 1) := .of_constantCoeff_zero' (by simp [hc])
  have hM : (1 + X) * geom (-1) = 1 := by simpa using geom_mul (-1)
  have hS := congrArg (substAlgHom hG) hM
  simp only [map_mul, map_add, map_one, coe_substAlgHom, subst_X hG] at hS
  have hD : derivative (R := ℚ) (log ℚ) = geom (-1) := by
    rw [deriv_log]
    simp [geom]
  rw [logOf_eq, derivative_subst hG, hD, map_sub, derivative_one, sub_zero]
  linear_combination (derivative (R := ℚ) F) * hS

theorem derivative_log_ratio :
    derivative (R := ℚ) (logOf F) = geom 1 - C (1 / 2 : ℚ) * geom (1 / 2) := by
  let c : ℚ⟦X⟧ := C (1 / 2 : ℚ)
  let U : ℚ⟦X⟧ := 1 - c * X
  let V : ℚ⟦X⟧ := 1 - X
  let D := derivative (R := ℚ) (logOf F)
  have hv : constantCoeff (X - 1 : ℚ⟦X⟧) ≠ 0 := by simp [map_sub]
  have hFV : F * V = U := by
    have h : F * (X - 1) = c * X - 1 := by
      rw [F, mul_assoc, PowerSeries.inv_mul_cancel _ hv, mul_one]
    dsimp [U, V]
    linear_combination -h
  have hDF : derivative (R := ℚ) F * V - F = -c := by
    have h := congrArg (derivative (R := ℚ)) hFV
    dsimp [U, V, c] at h ⊢
    simp only [Derivation.leibniz, map_sub, derivative_X, derivative_one, derivative_C,
      smul_eq_mul, zero_mul, one_mul, mul_one, add_zero, zero_add] at h
    linear_combination h
  have hc : c + c = 1 := by
    change C (1 / 2 : ℚ) + C (1 / 2 : ℚ) = (1 : ℚ⟦X⟧)
    rw [← map_add]
    norm_num
  have hD : D * (U * V) = c := by
    dsimp [U, V] at hFV hDF ⊢
    linear_combination (1 - X) ^ 2 * dlog_mul + (1 - X) * hDF -
      D * (1 - X) * hFV + hFV - hc
  have h1 : V * geom 1 = 1 := by simpa [V] using geom_mul (1 : ℚ)
  have h2 : U * geom (1 / 2) = 1 := geom_mul (1 / 2)
  have hE : (geom 1 - c * geom (1 / 2)) * (U * V) = c := by
    dsimp [U, V] at h1 h2 ⊢
    linear_combination (1 - c * X) * h1 - c * (1 - X) * h2 - hc
  have hne : U * V ≠ 0 := by
    intro h
    have hcc := congrArg constantCoeff h
    simp [U, V, map_sub] at hcc
  exact mul_right_cancel₀ hne (hD.trans hE.symm)

theorem log_coeff (m : ℕ) :
    coeff (m + 1) (logOf F) = (1 - 1 / 2 ^ (m + 1)) / ((m : ℚ) + 1) := by
  have h := coeff_derivative (logOf F) m
  rw [derivative_log_ratio, map_sub, coeff_C_mul] at h
  simp only [geom, coeff_mk, one_pow] at h
  rw [eq_div_iff (by positivity : (m : ℚ) + 1 ≠ 0)]
  have hpow : (1 / 2 : ℚ) * (1 / 2) ^ m = 1 / 2 ^ (m + 1) := by
    rw [← pow_succ']
    simp only [one_div, inv_pow]
  rw [hpow] at h
  exact h.symm

end OMA.LogRatio

theorem OMA.solution : type_of% @OMA.S_oeis_a131135.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a, OMA.LogRatio.log_coeff m, Nat.cast_add_one]
