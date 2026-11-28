import Mathlib

/-!
# A022008: Initial member of prime sextuples (p, p+4, p+6, p+10, p+12, p+16)

Source: https://oeis.org/A022008
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
There are infinitely many prime sextuples of the form `(p, p + 4, p + 6, p + 10, p + 12, p + 16)`.

Conventions:
- Primality is `Nat.Prime`.
-/

namespace OMA.S_oeis_a022008

theorem main :
    Set.Infinite
      {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 4) ∧ Nat.Prime (p + 6) ∧
        Nat.Prime (p + 10) ∧ Nat.Prime (p + 12) ∧ Nat.Prime (p + 16)} := by
  sorry

end OMA.S_oeis_a022008
