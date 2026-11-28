import OMAStatements.S_oeis_a087214
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A087214 (statement by @ivillar).
-- Idea (as in the entry's differential equation remark): (1 - x^2/2) * E = exp(x), so comparing
-- coefficients of x^(m+2) gives 2*a(m+2) - (m+2)*(m+1)*a(m) = 2 for every m; subtracting this identity
-- at m = n-3 from the one at m = n-2 is the conjectured recurrence.

namespace OMAA087214Helpers

open OMA.S_oeis_a087214

theorem hu : (1 - (1 / 2 : ℚ) • PowerSeries.X ^ 2) * E = PowerSeries.exp ℚ := by
  have h0 : PowerSeries.constantCoeff (1 - (1 / 2 : ℚ) • PowerSeries.X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp
  unfold E
  rw [mul_left_comm, PowerSeries.mul_inv_cancel _ h0, mul_one]

theorem hcoeff (m : ℕ) :
    PowerSeries.coeff (m + 2) E - 1 / 2 * PowerSeries.coeff m E = 1 / ((m + 2).factorial : ℚ) := by
  have h := congrArg (PowerSeries.coeff (m + 2)) hu
  rw [sub_mul, one_mul, map_sub, smul_mul_assoc, LinearMap.map_smul, PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), PowerSeries.coeff_exp] at h
  simpa using h

theorem key (m : ℕ) : 2 * a (m + 2) - ((m : ℚ) + 2) * ((m : ℚ) + 1) * a m = 2 := by
  have hf : (m + 2).factorial = (m + 2) * (m + 1) * m.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; ring
  have h := hcoeff m
  unfold a
  rw [hf] at h ⊢
  push_cast at h ⊢
  have hP : ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) ≠ 0 := by positivity
  have hP' := mul_one_div_cancel hP
  linear_combination (2 * (((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ))) * h + 2 * hP'

end OMAA087214Helpers

open OMA.S_oeis_a087214 OMAA087214Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a087214.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have e1 := key (k + 1)
  have e0 := key k
  simp only [show k + 1 + 2 = k + 3 from rfl] at e1
  push_cast at e1 ⊢
  linear_combination e1 - e0
