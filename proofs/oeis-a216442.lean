import OMAStatements.S_oeis_a216442

-- Problem: A216442: Numbers of the form 2^i + 3^j + 5^k, where i, j, k >= 0.
-- Upstream: formal-conjectures statements/oeis-a216442.lean:0 (declaration OMA.S_oeis_a216442.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: 2^1 + 3^1 = 5 = 2^2 + 3^0, so for every k the number 5 + 5^k has the two different
-- representations (1, 1, k) and (2, 0, k). The map k -> 5 + 5^k is injective.

namespace H09A216442

theorem inj : Function.Injective (fun k : ℕ => 5 + 5 ^ k) := by
  intro a b h
  have h1 : 5 + 5 ^ a = 5 + 5 ^ b := h
  exact Nat.pow_right_injective (by norm_num) (Nat.add_left_cancel h1)

theorem two_reps (k : ℕ) :
    ∃ i j k1 i' j' k1' : ℕ, (i, j, k1) ≠ (i', j', k1') ∧
      2 ^ i + 3 ^ j + 5 ^ k1 = 5 + 5 ^ k ∧ 2 ^ i' + 3 ^ j' + 5 ^ k1' = 5 + 5 ^ k := by
  refine ⟨1, 1, k, 2, 0, k, ?_, ?_, ?_⟩
  · intro h
    have h1 : (1 : ℕ) = 2 := congrArg Prod.fst h
    omega
  · norm_num
  · norm_num

end H09A216442

open H09A216442 in
theorem OMA.solution : type_of% @OMA.S_oeis_a216442.main := by
  exact Set.infinite_of_injective_forall_mem inj two_reps
