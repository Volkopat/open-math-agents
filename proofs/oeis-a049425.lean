import OMAStatements.S_oeis_a049425
import Mathlib

/-! Chain rule: the derivative of exp.subst P is exp.subst P times P' = 1 + 2X + X^2.
Coefficient n+2 of that identity, times (n+2)!, is the recurrence. -/

open PowerSeries OMA.S_oeis_a049425 in
theorem OMA.solution : type_of% @OMA.S_oeis_a049425.main := by
  intro n
  have hp : d⁄dX ℚ parameter = 1 + X * (1 + 1 + X) := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | _ | k <;> simp [parameter, coeff_X, coeff_X_pow] <;> norm_num
  have h := congrArg (coeff (n + 2)) (derivative_subst (f := exp ℚ)
    (HasSubst.of_constantCoeff_zero' (a := parameter) (by simp [parameter])))
  rw [derivative_exp, hp, mul_comm] at h
  simp [add_mul, mul_assoc, coeff_derivative] at h
  simp only [a, series, Nat.factorial_succ]
  push_cast
  linear_combination ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n.factorial : ℚ) * h
