import Mathlib

/-!
# A092517: Product of tau values for consecutive integers.

Source: https://oeis.org/A092517
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the maximum number of b > 0, which allows us to write (n+1)^2 as a sum of n+1
parts. Each part is of the form b^c and c is an integer >= 0 independent for each part.
It is conjectured that for all n the number of possible b reaches a(n).
-/

namespace OMA.S_oeis_a092517

def IsValidBase (n b : ℕ) : Prop :=
  0 < b ∧ ∃ f : Fin (n + 1) → ℕ, (∑ i, b ^ f i) = (n + 1) ^ 2

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ({b : ℕ | IsValidBase n b}).ncard =
        (Nat.divisors n).card * (Nat.divisors (n + 1)).card := by
  sorry

end OMA.S_oeis_a092517
