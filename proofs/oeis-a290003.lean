import OMAStatements.S_oeis_a290003
import Mathlib

open OMA.S_oeis_a290003 in
theorem OMA.solution : type_of% @OMA.S_oeis_a290003.main := by
  intro p hp h3
  have t1 : term (p + 1) 1 = 1 := by
    simp [term, firstChoose]
  have t2 : term (p + 1) p = 0 := by
    have e1 : (p + 1 - 1) / p = 1 := by
      rw [Nat.add_sub_cancel]
      exact Nat.div_self hp.pos
    have e2 : (p + 1 + p - 1) / p = 2 := by
      rw [show p + 1 + p - 1 = 2 * p by omega]
      exact Nat.mul_div_cancel _ hp.pos
    unfold term firstChoose
    rw [e1, e2, if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show p + 1 - 1 = p by omega, Nat.Prime.divisors hp]
  have hne : (1 : ℕ) ≠ p := by omega
  rw [Finset.sum_pair hne, t1, t2]
  norm_num
