import Mathlib

/-!
# A096537: E.g.f. exp(x*exp(2*x*exp(3*x*...)))

Source: https://oeis.org/A096537
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

E.g.f.: A(x) = exp(x*exp(2*x*exp(3*x*exp(...exp(n*x*exp(...))...)))), for n >= 1.
Conjecture: a(n) ~ 2 * Pi * n^(2*n + 1/2) / (exp(n) * (exp(1) - 1)^n).
-/

namespace OMA.S_oeis_a096537

noncomputable def expTrunc (d : ℕ) (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℚ)⁻¹ • (p ^ j))

noncomputable def tower (d : ℕ) : ℕ → ℕ → Polynomial ℚ
  | 0, _ => 1
  | m + 1, k => expTrunc d (((k : ℚ) • Polynomial.X) * tower d m (k + 1))

noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (tower n n 1).coeff n

theorem main :
    Filter.Tendsto
      (fun n : ℕ =>
        ((a n : ℝ) /
          (2 * Real.pi * (n : ℝ) ^ (2 * (n : ℝ) + 1 / 2) /
            (Real.exp (n : ℝ) * (Real.exp 1 - 1) ^ n))))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a096537
