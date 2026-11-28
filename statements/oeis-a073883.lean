import Mathlib

/-!
A073883: a(1)=1. For n > 1, a(n) = the smallest positive integer not included earlier such that the n-th partial sum is n times a prime.

Source: https://oeis.org/A073883
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectured not to be a permutation of the natural numbers. The numbers that have not been used before the 2000th term: 4, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, ...
-/

namespace OMA.S_oeis_a073883

/-- The sequence A073883 (1-indexed, with `a 0 = 0`). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    sInf {m : ℕ | 0 < m ∧ (∀ k : Fin (n + 1), a (k.1 + 1) ≠ m) ∧
      ∃ p : ℕ, Nat.Prime p ∧ (∑ k : Fin (n + 1), a (k.1 + 1)) + m = (n + 2) * p}

/-- Conjecture: A073883 is not a permutation of the positive integers (some positive integer never appears). -/
theorem main : ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → a n ≠ m := by sorry

end OMA.S_oeis_a073883
