import OMAStatements.S_oeis_a257889
import Mathlib

open OMA.S_oeis_a257889

theorem OMA.solution : type_of% @OMA.S_oeis_a257889.main := by
  intro a b h0 h1 hb hrec
  have b1 : b 1 = 2 := by
    rw [hb 1, pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, h0, h1]
  have a2 : a 2 = 2 := by
    have := (hrec 1 le_rfl).1
    rw [this, h1, b1]; norm_num
  have b2 : b 2 = 5 := by
    rw [hb 2, pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, h0, h1, a2]
  have a3 : a 3 = 5 := by
    have := (hrec 1 le_rfl).2
    rw [this, h1, b2]; norm_num
  intro n
  induction n with
  | zero => simp [a3]
  | succ k ih =>
    have e : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    rw [e, (hrec (3 * 2 ^ k) (Nat.one_le_iff_ne_zero.mpr (by positivity))).1]
    exact Dvd.dvd.mul_right ih _
