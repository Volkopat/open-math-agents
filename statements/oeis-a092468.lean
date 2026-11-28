import Mathlib

/-!
# OEIS A092468: growth ratio of a trinomial-type sum

Source: https://oeis.org/A092468
`a(n) = ∑_{i+j+k=n, 0 ≤ i ≤ j ≤ k ≤ n} (n+2k)! / (i! j! (3k)!)`. Conjecture (Kotesovec, 2021):
`a(n+1)/a(n) → (73 + 6√87)^(1/3)/3 + 13/(3 (73 + 6√87)^(1/3)) + 7/3 = 4.8751…`.

Conventions. The summand is computed in `ℚ` (it is not claimed to be an integer termwise);
`a n` is a rational number, and the limit is of the ratio of consecutive values.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a092468

open Filter Topology Real

/-- A092468. -/
def a (n : ℕ) : ℚ :=
  ∑ t ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun t => t.1 + t.2.1 + t.2.2 = n ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2),
    ((n + 2 * t.2.2).factorial : ℚ) /
      (t.1.factorial * t.2.1.factorial * (3 * t.2.2).factorial)

/-- The conjectured limit. -/
noncomputable def L : ℝ :=
  (73 + 6 * √87) ^ (1 / 3 : ℝ) / 3 + 13 / (3 * (73 + 6 * √87) ^ (1 / 3 : ℝ)) + 7 / 3

theorem main : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 L) := by
  sorry

end OMA.S_oeis_a092468
