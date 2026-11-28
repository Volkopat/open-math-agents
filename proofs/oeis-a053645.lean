import OMAStatements.S_oeis_a053645
import Mathlib

open OMA.S_oeis_a053645 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053645.main := by
  refine ⟨by simp [a], fun n hn => ?_⟩
  have := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
  have := Nat.lt_pow_succ_log_self one_lt_two (n - 1)
  have := @Nat.lt_two_pow_self (Nat.log 2 (n - 1) + 1)
  unfold a a036987
  split_ifs with hp
  · obtain ⟨k, -, hk⟩ := hp
    rw [show n = 2 ^ k by omega, Nat.log_pow (by norm_num)]
    simp
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (n := n) (m := Nat.log 2 (n - 1)) (by omega)
      (by by_contra; exact hp ⟨Nat.log 2 (n - 1) + 1, by omega, by omega⟩)]
    omega
