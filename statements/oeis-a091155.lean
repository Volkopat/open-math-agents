import Mathlib

/-!
# A091155: Numbers m such that m - 2^k is squarefree for all 1 <= 2^k < m.

Source: https://oeis.org/A091155
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Erdős conjectures that this sequence is infinite. It appears that m == 3 (mod 12)
except for m = 2, 4, 7 and 23.
-/

namespace OMA.S_oeis_a091155

def IsGood (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, 2 ^ k < m → Squarefree (m - 2 ^ k)

theorem main :
    {m : ℕ | IsGood m}.Infinite := by
  sorry

end OMA.S_oeis_a091155
