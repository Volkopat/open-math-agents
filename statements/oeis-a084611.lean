import Mathlib

/-!
# A084611: a(n) = sum of absolute values of coefficients of (1+x-x^2)^n.

Source: https://oeis.org/A084611
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Limit{n -> oo} a(n+1)/a(n) does not exist; however, lim{n -> oo} a(n)^(1/n) = sqrt(5) (conjecture).
-/

namespace OMA.S_oeis_a084611

noncomputable def P : Polynomial ℤ :=
  1 + Polynomial.X - Polynomial.X ^ 2

noncomputable def a (n : ℕ) : ℕ :=
  ((P ^ n).support).sum (fun k => ((P ^ n).coeff k).natAbs)

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds (Real.sqrt 5)) := by
  sorry

end OMA.S_oeis_a084611
