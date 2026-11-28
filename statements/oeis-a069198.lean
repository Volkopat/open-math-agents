import Mathlib

/-!
# A069198: Divergence of Collatz-Fibonacci sequence with a(1) = 1, a(2) = 6

Source: https://oeis.org/A069198
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069198: a(1)=1, a(2)=6, a(n+2)=(a(n+1)+a(n))/3 if 3 | (a(n+1)+a(n));
else (a(n+1)+a(n))/2 if 2 | (a(n+1)+a(n)); else a(n+1)+a(n).

Statement:
A Collatz-Fibonacci mixture. Conjecture: if a(1)=1 and a(2)=m different from 2 or 5,
the sequence diverges to infinity (in particular for a(2)=6).
-/

namespace OMA.S_oeis_a069198

/-- Collatz-Fibonacci step on the sum `s = a(n+1) + a(n)`. -/
def step (s : ℕ) : ℕ :=
  if 3 ∣ s then s / 3
  else if 2 ∣ s then s / 2
  else s

/-- `A069198` (1-indexed: `a 1 = 1`, `a 2 = 6`). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | n + 3 => step (a (n + 2) + a (n + 1))

theorem main :
    Filter.Tendsto a Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a069198
