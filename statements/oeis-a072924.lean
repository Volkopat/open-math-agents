import Mathlib

/-!
# A072924: Whiteman's conjecture on primes of the form floor(r^n)

Source: https://oeis.org/A072924
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A. L. Whiteman conjectured that the sequence floor(r^n) for any non-integer rational r > 1
always contains infinitely many primes.
-/

namespace OMA.S_oeis_a072924

theorem main :
    ∀ r : ℚ, 1 < r → r.den ≠ 1 →
      Set.Infinite { n : ℕ | Nat.Prime (Nat.floor (r ^ n)) } := by
  sorry

end OMA.S_oeis_a072924
