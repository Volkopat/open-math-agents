import Mathlib

/-!
A085245: Least k such that k*2^n + 1 is a semiprime.

Source: https://oeis.org/A085245
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

The first few values of n such that 78557*2^n + 1 is a semiprime, where k = 78557
(the conjectured smallest Sierpinski number), are: 2, 3, 7, 15, 17, 18, 24, 60, ...
Conjecture: there are infinitely many semiprimes of this form.
-/

namespace OMA.S_oeis_a085245

def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q

theorem main : {n : ℕ | IsSemiprime (78557 * 2 ^ n + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a085245
