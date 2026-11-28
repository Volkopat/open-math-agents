import Mathlib

/-!
# A007366: Numbers k such that phi(x) = k has exactly 2 solutions

Source: https://oeis.org/A007366
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `k` be a natural number such that the equation `φ(x) = k` (where `φ` is Euler's totient
function) has exactly 2 solutions `x < y` in `ℕ`.

Conjecture: The larger solution is always twice the smaller solution (`y = 2 * x`), or
equivalently, the smaller solution `x` is always odd.
-/

namespace OMA.S_oeis_a007366

theorem main :
    ∀ k x y : ℕ,
      x < y →
      { m : ℕ | Nat.totient m = k } = {x, y} →
      y = 2 * x := by
  sorry

end OMA.S_oeis_a007366
