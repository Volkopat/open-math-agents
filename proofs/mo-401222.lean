import OMAStatements.S_mo_401222

-- Problem: mo-401222, can binomial(2n, n) be divisible by 2n + 1 for a positive integer n?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes: the smallest example is n = 97, where 2n + 1 = 195 = 3 * 5 * 13 divides
-- binomial(194, 97). Mathlib’s fast binomial formula evaluates the witness in the kernel.

theorem OMA.solution : type_of% @OMA.S_mo_401222.main :=
  ⟨97, by decide, by rw [Nat.choose_eq_fast_choose]; decide +kernel⟩
