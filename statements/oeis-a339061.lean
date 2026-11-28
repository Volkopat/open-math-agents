import Mathlib

/-!
# A339061: gaps between successive harmonic thresholds

The threshold at level n is the least index k with H(k) at least n.
A339061(n) is the gap from that index to the corresponding index at n+1.
Adam Hugill's conjecture is stated for n > 1, as in the OEIS entry.

Source: https://oeis.org/A339061
-/

namespace OMA.S_oeis_a339061

open Real

/-- The least harmonic index whose sum is at least the given level. -/
noncomputable def threshold (n : ℕ) : ℕ :=
  sInf {k : ℕ | (n : ℚ) ≤ harmonic k}

/-- The number of additional terms to reach the next integer level. -/
noncomputable def a (n : ℕ) : ℕ := threshold (n + 1) - threshold n

/-- The rounded exponential approximation at an integer level. -/
noncomputable def rounded (n : ℕ) : ℕ :=
  ⌊exp ((n : ℝ) - eulerMascheroniConstant) + 1 / 2⌋₊

theorem main : ∀ n : ℕ, 1 < n →
    a n = rounded (n + 1) - rounded n := by
  sorry

end OMA.S_oeis_a339061
