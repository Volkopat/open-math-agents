import OMAStatements.S_oeis_a002716

-- Problem: A002716: An infinite coprime sequence defined by recursion.
-- Upstream: formal-conjectures statements/oeis-a002716.lean:0 (declaration OMA.S_oeis_a002716.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a002716

open OMA.S_oeis_a002716

lemma key (n : ℕ) : a (2 * n) = (2 : ℤ) ^ (2 ^ (n + 1)) - 2 ^ (2 ^ n) + 1 ∧
    a (2 * n + 1) = (2 : ℤ) ^ (2 ^ (n + 1)) + 1 := by
  induction n with
  | zero => norm_num [a]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : a (2 * (n + 1)) = a (2 * n + 1) ^ 2 - 3 * a (2 * n + 1) + 3 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, a, if_pos (by omega)]
    have e1 : a (2 * (n + 1) + 1) = a (2 * (n + 1)) + a (2 * n + 1) - 1 := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, a, if_neg (by omega)]
      rfl
    have hp : (2 : ℤ) ^ (2 ^ (n + 1 + 1)) = ((2 : ℤ) ^ (2 ^ (n + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (n + 1)]
    refine ⟨?_, ?_⟩
    · rw [e0, h1, hp]
      ring
    · rw [e1, e0, h1, hp]
      ring

lemma solve : ∀ n : ℕ, a (2 * n + 1) = 2 ^ (2 ^ (n + 1)) + 1 := fun n => (key n).2

end OMA.P_oeis_a002716

theorem OMA.solution : type_of% @OMA.S_oeis_a002716.main := OMA.P_oeis_a002716.solve
