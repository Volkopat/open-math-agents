import Mathlib

/-!
# A047363: Values of c/6 for which p^3 - c and p^3 + c are both prime infinitely often

Source: https://oeis.org/A047363
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A047363: Numbers that are congruent to {0, 2, 3, 4, 5} mod 7.

Statement:
Conjecture: Apart from 0, and when c is an even cube, the sequence gives the values of c/6
such that an infinite number of primes, p, result in both p^3+c and p^3-c being positive primes.
-/

namespace OMA.S_oeis_a047363

theorem main :
    ∀ m : ℕ, 0 < m → (∀ k : ℕ, 6 * m ≠ k ^ 3) →
      (Set.Infinite {p : ℕ | Nat.Prime p ∧ 6 * m < p ^ 3 ∧
        Nat.Prime (p ^ 3 - 6 * m) ∧ Nat.Prime (p ^ 3 + 6 * m)} ↔
        m % 7 = 0 ∨ m % 7 = 2 ∨ m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5) := by
  sorry

end OMA.S_oeis_a047363
