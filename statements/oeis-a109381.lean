import Mathlib

/-!
# OEIS A109381: maximum factorial-base digit of n² tends to infinity

Source: https://oeis.org/A109381
`a n` is the maximum digit of `n²` written in the factorial number system. Conjecture:
`a(n) → ∞`.

Conventions. The factorial-base digit of `m` at position `k ≥ 1` is `⌊m / k!⌋ mod (k + 1)`;
the maximum is taken over the positions `k = 1, …, m`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a109381

open Filter

/-- Maximum factorial-base digit of `m`. -/
def maxDigit (m : ℕ) : ℕ := (Finset.Icc 1 m).sup fun k => m / k.factorial % (k + 1)

theorem main : Tendsto (fun n : ℕ => maxDigit (n ^ 2)) atTop atTop := by
  sorry

end OMA.S_oeis_a109381
