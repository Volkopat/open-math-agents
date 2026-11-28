import OMAStatements.S_oeis_a085096

-- Problem: A085096: Index of the first occurrence of n in A082744, or 0 if n does not occur in the sequence A082744.
-- Upstream: formal-conjectures statements/oeis-a085096.lean:0 (declaration OMA.S_oeis_a085096.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: k = 1120 is a counterexample to the second form (it is the listed term a(11) = 1120):
-- 11 * 1120 + 1 = 12321 is a palindrome, while 1121, 2241, 3361, 4481, 5601, 6721, 7841, 8961,
-- 10081 and 11201 are not.

open OMA.S_oeis_a085096 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085096.main) := by
  intro h
  have hpal : IsPal (11 * 1120 + 1) := by
    unfold IsPal
    norm_num
  obtain ⟨j, hj1, hj2, hj⟩ := h.2 1120 (by norm_num) hpal
  unfold IsPal at hj
  interval_cases j <;> norm_num at hj
