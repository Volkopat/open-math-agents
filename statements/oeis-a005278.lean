import Mathlib

/-!
# A005278: All Noncototients Are Even

Source: https://oeis.org/A005278
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

A natural number `k` is a noncototient if the equation `x - φ(x) = k` has no solution `x : ℕ`.

Conjecture (implied by the strong Goldbach conjecture): Every noncototient is even; equivalently,
every odd natural number can be written as `x - φ(x)` for some `x : ℕ`.
-/

namespace OMA.S_oeis_a005278

theorem main :
    ∀ k : ℕ, (∀ x : ℕ, x - Nat.totient x ≠ k) → Even k := by
  sorry

end OMA.S_oeis_a005278
