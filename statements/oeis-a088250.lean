import Mathlib

/-!
# A088250: Smallest k such that r*k + 1 is prime for all r = 1 to n

Source: https://oeis.org/A088250
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the smallest positive integer k such that r*k + 1 is prime for all
r = 1, 2, ..., n.
Conjectures:
(1) The sequence is infinite (such a k exists for every n >= 1).
(2) For every n >= 1, there are infinitely many arithmetic progressions of n
    consecutive primes.
-/

namespace OMA.S_oeis_a088250

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ ∀ r : ℕ, 1 ≤ r → r ≤ n → (r * k + 1).Prime) ∧
    (∀ n : ℕ, 1 ≤ n →
      Set.Infinite {i : ℕ | ∃ d : ℕ, 0 < d ∧
        ∀ j : ℕ, j < n → Nat.nth Nat.Prime (i + j) = Nat.nth Nat.Prime i + j * d}) := by
  sorry

end OMA.S_oeis_a088250
