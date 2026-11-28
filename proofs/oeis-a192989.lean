import OMAStatements.S_oeis_a192989
import Mathlib.RingTheory.PowerSeries.Derivative

open OMA.S_oeis_a192989
open PowerSeries

private theorem series_differential :
    derivative ℚ egf = (C (3 : ℚ) + C (6 : ℚ) * X + C (3 : ℚ) * X ^ 2) * egf := by
  unfold egf
  have hs : HasSubst (((1 + X : ℚ⟦X⟧) ^ 3) - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  rw [derivative_subst hs, derivative_exp]
  simp only [map_sub, derivative_one, sub_zero, derivative_pow, map_add, derivative_X, zero_add,
    mul_one, map_ofNat]
  ring

private theorem coefficient_step (n : ℕ) :
    coeff (n + 3) egf * ((n : ℚ) + 3) =
      3 * coeff (n + 2) egf + 6 * coeff (n + 1) egf + 3 * coeff n egf := by
  have h := congrArg (coeff (n + 2)) series_differential
  have shift (k : ℕ) (hk : k ≤ n + 2) :
      coeff (n + 2) (X ^ k * egf) = coeff (n + 2 - k) egf := by
    rw [coeff_X_pow_mul', if_pos hk]
  have shiftOne := shift 1 (by omega)
  have shiftTwo := shift 2 (by omega)
  simp only [pow_one, show n + 2 - 1 = n + 1 by omega,
    show n + 2 - 2 = n by omega] at shiftOne shiftTwo
  simp only [coeff_derivative, add_mul, map_add, mul_assoc, coeff_C_mul,
    shiftOne, shiftTwo] at h
  push_cast at h
  linarith only [h]

private theorem shifted_recurrence (n : ℕ) :
    a (n + 3) - 3 * a (n + 2) - 6 * ((n : ℚ) + 2) * a (n + 1) -
      3 * ((n : ℚ) + 2) * ((n : ℚ) + 1) * a n = 0 := by
  simp only [a, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  linear_combination ((n.factorial : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2)) *
    coefficient_step n

theorem OMA.solution : type_of% @OMA.S_oeis_a192989.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, Nat.cast_add, Nat.cast_ofNat]
  linear_combination shifted_recurrence m
