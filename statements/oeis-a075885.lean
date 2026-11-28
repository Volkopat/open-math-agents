import Mathlib

/-!
# A075885: a(n) = 1 + n + n*[n/2] + n*[n/2]*[n/3] + n*[n/2]*[n/3]*[n/4] +... where [x]=floor(x).

Source: https://oeis.org/A075885
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: limit a(n)^(1/n) = L where L = 2.200161058099... is the geometric mean of Luroth expansions, where log(L) = Sum_{n>=1} log(n)/(n*(n+1)) = 0.7885305659115... (cf. A085361).
-/

namespace OMA.S_oeis_a075885

/-- The sequence `a(n) = 1 + n + n*⌊n/2⌋ + n*⌊n/2⌋*⌊n/3⌋ + ...`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ∏ j ∈ Finset.Icc 1 k, (n / j)

/-- The geometric mean constant `L = exp(∑_{n≥1} log(n) / (n*(n+1)))`. -/
noncomputable def L : ℝ :=
  Real.exp (∑' n : ℕ, Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)))

/-- Conjecture: `a(n)^(1/n) → L` as `n → ∞`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds L) := by sorry

end OMA.S_oeis_a075885
