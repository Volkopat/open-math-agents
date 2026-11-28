import Mathlib

/-!
# A088144: Distribution of mu(p - 1) over primes p

Source: https://oeis.org/A088144
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let A = Product_{q prime} (1 - 1 / (q * (q - 1))) be Artin's constant.
By Mirsky's theorem, sum_{p <= x} mu(p - 1)^2 ~ A * x / log x.
Conjecture (OEIS entry, 2003):
  sum_{p <= x, mu(p - 1) = 1} 1 = (A / 2) * x / log x + o(x / log x)
and
  sum_{p <= x, mu(p - 1) = -1} 1 = (A / 2) * x / log x + o(x / log x)
as x -> infinity.
-/

namespace OMA.S_oeis_a088144

open Filter Topology

/-- Artin's constant `∏_{q prime} (1 - 1 / (q * (q - 1)))`. -/
noncomputable def artinConstant : ℝ :=
  ∏' q : {p : ℕ // p.Prime}, (1 - (1 : ℝ) / ((q.1 : ℝ) * ((q.1 : ℝ) - 1)))

/-- Number of primes `p ≤ x` with `μ(p - 1) = s`. -/
noncomputable def primeMoebiusCount (s : ℤ) (x : ℝ) : ℕ :=
  ((Finset.range (Nat.floor x + 1)).filter
    (fun p => p.Prime ∧ ArithmeticFunction.moebius (p - 1) = s)).card

theorem main :
    Tendsto (fun x : ℝ => (primeMoebiusCount 1 x : ℝ) / (x / Real.log x))
      atTop (𝓝 (artinConstant / 2)) ∧
    Tendsto (fun x : ℝ => (primeMoebiusCount (-1) x : ℝ) / (x / Real.log x))
      atTop (𝓝 (artinConstant / 2)) := by
  sorry

end OMA.S_oeis_a088144
