import Mathlib

/-!
# A396605: The zeros of the minimum totient-divisor gap have density zero

Source: https://oeis.org/A396605

For n ≥ 2, A396605 minimizes |n - d * φ(d)| over divisors d > 1 of n,
including d=n. Its value is zero if and only if some such divisor
satisfies n = d * φ(d). This witness definition describes the zero set
directly. There are no terms at indices 0 or 1.

The OEIS entry credits Walther Janous and the solution of Monthly
Problem 6588 for a sharper square-root asymptotic. The density-zero
claim here only requires the elementary growth of the totient.
-/

open Filter Topology

namespace OMA.S_oeis_a396605

/-- Zero indices of the OEIS minimum absolute gap. -/
def zeroAt (n : ℕ) : Prop :=
  ∃ d : ℕ, 1 < d ∧ d ∣ n ∧ n = d * d.totient

/-- Number of zero indices at most N. -/
noncomputable def zeroCount (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range (N+1)).filter zeroAt).card

/-- The set of indices with zero minimum gap has natural density zero. -/
theorem main : Tendsto (fun N : ℕ => (zeroCount N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a396605
