import Mathlib

/-!
# A047222: Values of c/6 for which p^2 - c and p^2 + c are both prime infinitely often

Source: https://oeis.org/A047222
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A047222: Numbers that are congruent to {0, 2, 3} mod 5.

Statement:
Conjecture: Apart from 0, the sequence gives the values for c/6, such that an infinite number
of primes, p, result in both p^2-c and p^2+c being positive primes, except when c is a square.
-/

namespace OMA.S_oeis_a047222

theorem main :
    ∀ m : ℕ, 0 < m → ¬ IsSquare (6 * m) →
      (Set.Infinite {p : ℕ | Nat.Prime p ∧ 6 * m < p ^ 2 ∧
        Nat.Prime (p ^ 2 - 6 * m) ∧ Nat.Prime (p ^ 2 + 6 * m)} ↔
        m % 5 = 0 ∨ m % 5 = 2 ∨ m % 5 = 3) := by
  sorry

end OMA.S_oeis_a047222
