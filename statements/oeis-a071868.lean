import Mathlib

/-!
# A071868: Number of integers k (1 <= k <= n) such that k^2+1 is prime

Source: https://oeis.org/A071868
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Hardy and Littlewood conjectured that:
a(n) ~ c * n / (2 log n) where (the OEIS text writes c sqrt(n)/log(n), which is the
Hardy-Littlewood count of primes k^2+1 up to x = n^2; in terms of k <= n it is c n/(2 log n))
c = Product_{p odd prime} (1 - (-1)^((p-1)/2) / (p-1)) = 1.3728...
-/

namespace OMA.S_oeis_a071868

open Filter Topology

/-- Number of integers `k` with `1 ≤ k ≤ n` such that `k^2 + 1` is prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.Prime (k ^ 2 + 1))).card

/-- Partial product up to `N` for the Hardy-Littlewood constant
`∏_{p odd prime} (1 - (-1)^((p-1)/2) / (p-1))`. -/
noncomputable def constPartialProd (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 3 N).filter Nat.Prime,
    (1 - ((-1 : ℝ) ^ ((p - 1) / 2)) / ((p : ℝ) - 1))

theorem main :
    ∃ c : ℝ,
      Tendsto constPartialProd atTop (𝓝 c) ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / (c * (n : ℝ) / (2 * Real.log (n : ℝ))))
        atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a071868
