import OMAStatements.S_oeis_a076035
import Mathlib

open PowerSeries OMA.S_oeis_a076035 in
theorem OMA.solution : type_of% @OMA.S_oeis_a076035.main := by
  intro n hn
  have h : denominator⁻¹ - C 4 * ((1 - 3 * X * catalanGF) * denominator⁻¹) = C (-3) * (denominator * denominator⁻¹) := by
    simp only [denominator, map_neg, map_ofNat]
    ring
  rw [PowerSeries.mul_inv_cancel _ (by simp [denominator]), mul_one] at h
  have := congrArg (coeff n) h
  rw [map_sub, coeff_C_mul, coeff_C, if_neg (by omega), sub_eq_zero] at this
  exact this
