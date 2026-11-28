import OMAStatements.S_oeis_a173526
import Mathlib

open OMA.S_oeis_a173526 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173526.main := by
  refine ⟨by simp [a, A053827], fun i j hj => ?_⟩
  obtain h | h := Nat.eq_zero_or_pos (6*i+j)
  · simp [a, A053827, show i = 0 by omega, show j = 0 by omega]
  · simp [a, A053827, Nat.digits_def' (by norm_num : 1 < 6) h, show (6*i+j)%6 = j by omega,
      show (6*i+j)/6 = i by omega]
    ring
