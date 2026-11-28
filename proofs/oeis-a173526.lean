import OMAStatements.S_oeis_a173526

-- Problem: A173526: a(n) = 1 + A053827(n-1), where A053827 is the sum-of-digits function in base 6.
-- Upstream: formal-conjectures statements/oeis-a173526.lean:0 (declaration OMA.S_oeis_a173526.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for 0 <= j <= 5 the base-6 digits of 6*i + j are j followed by the base-6 digits
-- of i (Nat.digits_def'), so A053827(6*i + j) = A053827(i) + j, and A053827(0) = 0.

namespace L05A173526

open OMA.S_oeis_a173526

theorem s_zero : A053827 0 = 0 := by
  unfold A053827
  rw [Nat.digits_zero, List.sum_nil]

theorem key (i j : ℕ) (hj : j < 6) : A053827 (6 * i + j) = A053827 i + j := by
  rcases Nat.eq_zero_or_pos (6 * i + j) with h | h
  · have hi : i = 0 := by omega
    have hj0 : j = 0 := by omega
    rw [h, hi, hj0, Nat.add_zero]
  · have e : Nat.digits 6 (6 * i + j) = (6 * i + j) % 6 :: Nat.digits 6 ((6 * i + j) / 6) :=
      Nat.digits_def' (by norm_num) h
    unfold A053827
    rw [e, show (6 * i + j) % 6 = j by omega, show (6 * i + j) / 6 = i by omega, List.sum_cons]
    omega

end L05A173526

open OMA.S_oeis_a173526 L05A173526 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173526.main := by
  refine ⟨?_, ?_⟩
  · unfold a
    rw [Nat.sub_self, s_zero]
  · intro i j hj
    unfold a
    rw [show 6 * i + j + 1 - 1 = 6 * i + j by omega, show i + 1 - 1 = i by omega, key i j hj]
    omega
