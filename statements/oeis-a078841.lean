import Mathlib

/-!
# OEIS A078841: diagonal of the almost-prime table

Source: https://oeis.org/A078841
`a n` is the `(n+1)`-st integer that is an `n`-almost prime (has exactly `n` prime factors
counted with multiplicity). Conjecture (Wilson v, 2007): `a(n+1)/a(n) → 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a078841

open Filter Topology

/-- The `(n+1)`-st `n`-almost prime. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => 1 ≤ m ∧ m.primeFactorsList.length = n) n

theorem main : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a078841
