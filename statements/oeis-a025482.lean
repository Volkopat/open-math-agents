import Mathlib

/-!
# A025482: a(0) = 0; a(n) = a(n/3)/3 if 3 | n and 3 | a(n/3); else a(n-1) + 1

Source: https://oeis.org/A025482
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: The sequence defined by `a(0) = 0`, `a(n) = a(n / 3) / 3` if `n ≡ 0 (mod 3)`
and `a(n / 3) ≡ 0 (mod 3)`, and `a(n) = a(n - 1) + 1` otherwise, is bounded above by
`a(257) = 17`.
-/

namespace OMA.S_oeis_a025482

/-- The recursive sequence A025482. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 3 = 0 ∧ a ((n + 1) / 3) % 3 = 0 then
      a ((n + 1) / 3) / 3
    else
      a n + 1

theorem main :
    a 257 = 17 ∧ ∀ n : ℕ, a n ≤ 17 := by
  sorry

end OMA.S_oeis_a025482
