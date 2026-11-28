import Mathlib

/-!
# A092950: Beginning with n, add the next number, subtract the previous number and so on until one gets a prime, or 0 if no such prime is reached.

Source: https://oeis.org/A092950
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(p) = p, p is a prime. If the process is continued until a 1 is subtracted the result
is n^2. Conjecture: No term is zero.
-/

namespace OMA.S_oeis_a092950

def seqVal (n j : ℕ) : ℕ :=
  let k := j / 2
  if j % 2 = 0 then
    n + k * (k + 1)
  else
    n + k * (k + 1) + (n + k + 1)

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ j : ℕ, j ≤ 2 * (n - 1) ∧ Nat.Prime (seqVal n j) := by
  sorry

end OMA.S_oeis_a092950
