import Mathlib

/-!
# A088258: Factorials having at least one prime neighbor

Source: https://oeis.org/A088258
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Factorials F = n! which have at least one prime neighbor, i.e., F + 1 or F - 1
(or both) are prime.
Conjecture: The sequence is infinite, but there are only finitely many members
sandwiched between twin primes (both F - 1 and F + 1 prime).
-/

namespace OMA.S_oeis_a088258

theorem main :
    Set.Infinite {n : ℕ | (n.factorial + 1).Prime ∨ (n.factorial - 1).Prime} ∧
    Set.Finite {n : ℕ | (n.factorial + 1).Prime ∧ (n.factorial - 1).Prime} := by
  sorry

end OMA.S_oeis_a088258
