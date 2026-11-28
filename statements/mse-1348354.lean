import Mathlib

/-!
# Brocard's Problem

Source: https://math.stackexchange.com/questions/1348354/what-steps-have-been-taken-so-far-to-solve-brocards-problem
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Brocard's problem asks whether the Diophantine equation
`n! + 1 = m^2`
has any solutions in natural numbers `(n, m)` other than `n = 4, 5, 7`
(giving `(4, 5), (5, 11), (7, 71)`).

## Formalization Notes
We state the conjecture that every natural-number solution `(n, m)` to
`n! + 1 = m^2` has `n ∈ {4, 5, 7}`.
-/

namespace OMA.S_mse_1348354

theorem main :
    ∀ n m : ℕ, n.factorial + 1 = m ^ 2 → n = 4 ∨ n = 5 ∨ n = 7 := by
  sorry

end OMA.S_mse_1348354
