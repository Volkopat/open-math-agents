import OMAReductions.R_wp_marshall_hall_s_conjecture_R1
import Mathlib

theorem OMA.solution : OMA.R_wp_marshall_hall_s_conjecture_R1.H1 := fun k y hk h => by
  have e : |y| - k^3 ≠ 0 := fun e => h (by rw [← sq_abs, sub_eq_zero.1 e]; ring)
  rw [← sq_abs y, show (k^2)^3 = (k^3)^2 by ring, sq_sub_sq, abs_mul]
  nlinarith [Int.one_le_abs e, le_abs_self (|y|+k^3), abs_nonneg y, pow_pos hk 3]
