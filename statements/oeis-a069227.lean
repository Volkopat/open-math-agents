import Mathlib

/-!
# A069227: Divergence of Collatz-Fibonacci sequence dividing by gcd(sum, 4) with a(2) = 2

Source: https://oeis.org/A069227
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A069227: a(1)=1, a(2)=2; a(n+2) = (a(n+1) + a(n))/b(n) where
b(n) = gcd(a(n+1) + a(n), 4).

Statement:
Conjecture: sequence diverges to infinity.
-/

namespace OMA.S_oeis_a069227

/-- `A069227` (1-indexed: `a 1 = 1`, `a 2 = 2`). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 =>
    let s := a (n + 2) + a (n + 1)
    s / Nat.gcd s 4

theorem main :
    Filter.Tendsto a Filter.atTop Filter.atTop := by
  sorry

end OMA.S_oeis_a069227
