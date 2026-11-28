import Mathlib

/-!
# A069003: Upper bound 4*sqrt(n+1) on smallest d with n^2 + d^2 prime

Source: https://oeis.org/A069003
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069003: Smallest integer d such that n^2 + d^2 is a prime number.

Statement:
Conjecture: a(n) does not exceed 4*sqrt(n+1) for any positive integer n.
-/

namespace OMA.S_oeis_a069003

/-- Smallest natural number `d` such that `n^2 + d^2` is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {d : ℕ | Nat.Prime (n ^ 2 + d ^ 2)}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∃ d : ℕ, Nat.Prime (n ^ 2 + d ^ 2)) ∧
      (a n : ℝ) ≤ 4 * Real.sqrt ((n + 1 : ℝ)) := by
  sorry

end OMA.S_oeis_a069003
