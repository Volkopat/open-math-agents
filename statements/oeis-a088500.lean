import Mathlib

/-!
# A088500: Expansion of e.g.f. 1/(1+2*log(1-x))

Source: https://oeis.org/A088500
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: a(n) = Integral_{x=0..oo} Pochhammer(2*x, n)/exp(x) dx,
where a(n) is the n-th coefficient of the exponential generating function
1 / (1 + 2 * log(1 - x)).
-/

namespace OMA.S_oeis_a088500

/-- The exponential generating function f(x) = 1 / (1 + 2 * log(1 - x)). -/
noncomputable def egf (x : ℝ) : ℝ :=
  (1 + 2 * Real.log (1 - x))⁻¹

/-- The n-th term a(n), given by the n-th derivative of the e.g.f. at 0. -/
noncomputable def a (n : ℕ) : ℝ :=
  iteratedDeriv n egf 0

/-- The rising factorial (Pochhammer symbol) (z)_n = ∏_{k=0}^{n-1} (z + k). -/
def pochhammer (z : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (z + (k : ℝ))

theorem main :
    ∀ n : ℕ,
      a n = ∫ x in Set.Ioi (0 : ℝ), pochhammer (2 * x) n / Real.exp x := by
  sorry

end OMA.S_oeis_a088500
