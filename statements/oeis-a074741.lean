import Mathlib

/-!
# A074741: Sum of squares of gaps between consecutive primes

Source: https://oeis.org/A074741
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

D. R. Heath-Brown's conjecture (recorded in the entry):
`∑_{p_n ≤ N} (p_n - p_{n-1})² ~ 2 N log N`.

## Encoding

* With `p_k = Nat.nth Nat.Prime k` (`p_0 = 2`), the sum runs over the `k ≥ 1` with `p_k ≤ N`.
* `~` means the ratio to `2 N log N` tends to `1` as the real `N → ∞`.
* Marek Wolf's conjecture in the same entry has an unspecified error term and is not stated.
-/

namespace OMA.S_oeis_a074741

open Filter Topology

/-- `∑_{1 ≤ k, p_k ≤ N} (p_k - p_{k-1})²`. -/
noncomputable def S (N : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (Nat.primeCounting ⌊N⌋₊)).filter (1 ≤ ·),
    ((Nat.nth Nat.Prime k : ℝ) - Nat.nth Nat.Prime (k - 1)) ^ 2

theorem main : Tendsto (fun N : ℝ => S N / (2 * N * Real.log N)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a074741
