import OMAStatements.S_oeis_a358982

-- Problem: A358982: In base 10, for all numbers with n digits, a(n) is the number where the sum of digits of a(n) minus the sum of the last n digits of a(n)^3 reaches a record maximum.
-- Upstream: formal-conjectures statements/oeis-a358982.lean:0 (declaration OMA.S_oeis_a358982.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: 587 has digit sum 20 and 587^3 = 202262003 has digit sum 17. Appending zeros changes no
-- digit sum, so every x = 10^N * 587 works, and these numbers are unbounded.

namespace H13A358982

open OMA.S_oeis_a358982

theorem digitSum_pow_mul (k m : ℕ) (hm : 0 < m) : digitSum (10 ^ k * m) = digitSum m := by
  unfold digitSum
  rw [Nat.digits_base_pow_mul (b := 10) (k := k) (by norm_num) hm]
  simp

end H13A358982

open OMA.S_oeis_a358982 H13A358982 in
theorem OMA.solution : type_of% @OMA.S_oeis_a358982.main := by
  have h1 : digitSum 587 = 20 := by
    unfold digitSum
    norm_num
  have h2 : digitSum 202262003 = 17 := by
    unfold digitSum
    norm_num
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨10 ^ N * 587, ?_, ?_⟩
  · show digitSum ((10 ^ N * 587) ^ 3) < digitSum (10 ^ N * 587)
    rw [show (10 ^ N * 587) ^ 3 = 10 ^ (3 * N) * 202262003 by ring,
      digitSum_pow_mul (3 * N) 202262003 (by norm_num), digitSum_pow_mul N 587 (by norm_num),
      h1, h2]
    norm_num
  · have h : N < 10 ^ N := Nat.lt_pow_self (by norm_num)
    omega
