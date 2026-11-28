import Mathlib

/-!
# A097386: Numbers n such that (largest digit of n)^(smallest digit of n) + n is prime

Source: https://oeis.org/A097386
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let f(x) = (largest digit of x)^(smallest digit of x) + x.
Conjecture: There are infinitely many positive integers n such that f(n) and f(n+1) are both prime.
-/

namespace OMA.S_oeis_a097386

def maxDigit (x : ℕ) : ℕ :=
  (Nat.digits 10 x).foldl max 0

def minDigit (x : ℕ) : ℕ :=
  (Nat.digits 10 x).foldl min 9

def f (x : ℕ) : ℕ :=
  (maxDigit x) ^ (minDigit x) + x

theorem main :
    Set.Infinite {n : ℕ | 0 < n ∧ Nat.Prime (f n) ∧ Nat.Prime (f (n + 1))} := by
  sorry

end OMA.S_oeis_a097386
