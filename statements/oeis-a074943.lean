import Mathlib

/-!
# A074943: a(n) = tau(n) mod 3.

Source: https://oeis.org/A074943
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Asymptotic mean: Limit{m->oo} (1/m) * Sum{k=1..m} a(k) = 9*zeta(3)/Pi^2 = 1.0961...
-/

namespace OMA.S_oeis_a074943

/-- `a(n) = tau(n) mod 3`, where `tau(n)` is the number of positive divisors of `n`. -/
def a (n : ℕ) : ℕ :=
  n.divisors.card % 3

/-- Conjecture: the Cesàro mean of `tau(k) mod 3` converges to `9 * zeta(3) / pi^2`. -/
theorem main :
    Filter.Tendsto
      (fun m : ℕ => (∑ k ∈ Finset.Icc 1 m, (a k : ℝ)) / (m : ℝ))
      Filter.atTop
      (nhds (9 * (∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℝ) ^ 3)) / Real.pi ^ 2)) := by sorry

end OMA.S_oeis_a074943
