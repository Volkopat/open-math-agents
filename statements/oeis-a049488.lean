import Mathlib

/-!
# A049488: Infinitude of primes p such that p + 16 is prime

Source: https://oeis.org/A049488
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A049488: Primes p such that p + 16 is prime.

Statement:
Using the Elliott-Halberstam conjecture, Goldston et al. prove that there are an infinite
number of primes here. `main` states the infinitude unconditionally.
-/

namespace OMA.S_oeis_a049488

theorem main :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 16)} := by
  sorry

end OMA.S_oeis_a049488
