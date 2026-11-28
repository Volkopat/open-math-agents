import Mathlib

/-!
# A047800: Number of different values of i² + j² for i, j in [0, n]

Source: https://oeis.org/A047800
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Vaclav Kotesovec, after Landau and Erdős): `a(n) ~ c · n² / √(log n)` with
`c = 0.79…`.

## Encoding

* `a n` is the number of distinct values `i² + j²` with `0 ≤ i, j ≤ n`.
* The conjecture is stated as the existence of a positive limit `c` of
  `a(n) / (n² / √(log n))`; the numerical value `0.79…` is only an empirical approximation and
  is not part of the statement.
-/

namespace OMA.S_oeis_a047800

open Filter Topology

/-- `a n`: number of distinct values of `i² + j²` for `i, j ∈ [0, n]`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image fun p => p.1 ^ 2 + p.2 ^ 2).card

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) ^ 2 / Real.sqrt (Real.log n))) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a047800
