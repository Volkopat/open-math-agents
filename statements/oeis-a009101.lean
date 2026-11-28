import Mathlib

/-!
# A009101: Fixed point when iterating f(x) = x + product of digits of x

Source: https://oeis.org/A009101
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
Let `f(x) = x + (product of base-10 digits of x)`.
It is conjectured that for every natural number `n`, iterating `f` starting from `n`
reaches a fixed point in a finite number of steps.

Conventions:
- For `x = 0`, the product of digits is `0`, so `f(0) = 0`.
- For `x > 0`, the product of base-10 digits is `(Nat.digits 10 x).prod`.
-/

namespace OMA.S_oeis_a009101

def digitProd (x : ℕ) : ℕ :=
  if x = 0 then 0 else (Nat.digits 10 x).prod

def step (x : ℕ) : ℕ :=
  x + digitProd x

theorem main : ∀ n : ℕ, ∃ k : ℕ, step (step^[k] n) = step^[k] n := by
  sorry

end OMA.S_oeis_a009101
