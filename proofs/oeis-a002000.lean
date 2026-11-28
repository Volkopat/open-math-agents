import OMAStatements.S_oeis_a002000
import Mathlib

open OMA.S_oeis_a002000

/-- The shift by the fixed point -2 gains two powers of three at every step. -/
private theorem shift_dvd (n : ℕ) : (3 : ℤ) ^ (2*n+2) ∣ a n + 2 := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    have h : (3 : ℤ) ∣ a n - 1 := by
      rw [show a n - 1 = (a n + 2) - 3 by ring]
      exact dvd_sub ((dvd_pow_self 3 (by omega)).trans ih) (dvd_refl 3)
    rw [show 2*(n+1)+2 = (2*n+2)+2 by omega, pow_add,
      show a (n+1) + 2 = (a n + 2) * (a n - 1)^2 by rw [a]; ring]
    exact mul_dvd_mul ih (pow_dvd_pow_of_dvd h 2)

theorem OMA.solution : type_of% @OMA.S_oeis_a002000.main := by
  intro n r hr
  rw [Int.modEq_iff_dvd,
    show a n - a (n+1) = (a n + 2) * (a n * (2 - a n)) by rw [a]; ring]
  exact ((pow_dvd_pow 3 (by omega)).trans (shift_dvd n)).mul_right _
