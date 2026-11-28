import Mathlib

/-!
# A031157: Numbers that are both lucky and prime

Source: https://oeis.org/A031157
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
There are infinitely many numbers that are both lucky (A000959) and prime.

Conventions:
The lucky sieve begins with the odd positive integers sieve(0, k) = 2*k + 1 (0-indexed).
At step n + 1, letting s = sieve(n, n + 1) be the next surviving step size, we delete
every s-th element (1-indexed), which maps 0-indexed position k to k + k / (s - 1).
The k-th lucky number (0-indexed) is lucky(k) = sieve(k, k) = 1, 3, 7, 9, 13, 15, 21, ...
-/

namespace OMA.S_oeis_a031157

/-- State of the lucky-number sieve after n elimination rounds (0-indexed). -/
def luckySieve : ℕ → ℕ → ℕ
  | 0, k => 2 * k + 1
  | n + 1, k =>
    let s := luckySieve n (n + 1)
    luckySieve n (k + k / (s - 1))

/-- The k-th lucky number (0-indexed: 1, 3, 7, 9, 13, 15, 21, ...). -/
def lucky (k : ℕ) : ℕ :=
  luckySieve k k

/-- Predicate that m is a lucky number. -/
def IsLucky (m : ℕ) : Prop :=
  ∃ k : ℕ, lucky k = m

/-- Conjecture: There are infinitely many lucky primes. -/
theorem main : {p : ℕ | IsLucky p ∧ Nat.Prime p}.Infinite := by
  sorry

end OMA.S_oeis_a031157
