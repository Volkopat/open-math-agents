import Mathlib

/-!
# A082382: Table which contains in row n the track of n->A003132(n) until reaching 1 or 4.

Source: https://oeis.org/A082382
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Each sequence terminates with 1 or the 4 16 37 58 89 145 42 20 4... loop.
-/

namespace OMA.S_oeis_a082382

def sumSqDigits (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map (fun d => d * d)).sum

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (sumSqDigits^[k] n) = 1 ∨ (sumSqDigits^[k] n) = 4 := by
  sorry

end OMA.S_oeis_a082382
