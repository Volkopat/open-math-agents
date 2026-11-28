import Mathlib

/-!
# A361035: parity of a factorial quotient

Peter Bala conjectured that this sequence is odd exactly at indices `2^k - 3`
for `k ≥ 2`. The sequence starts at `n = 0`.

Source: https://oeis.org/A361035
Credit: @dwilfand-sys
-/

namespace OMA.S_oeis_a361035

/-- The factorial quotient defining OEIS A361035, with natural division. -/
def a (n : ℕ) : ℕ :=
  9979200 * (4 * n).factorial / (n.factorial * (n + 3).factorial ^ 3)

/-- Peter Bala's parity conjecture for A361035. -/
theorem main : ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k - 3 := by
  sorry

end OMA.S_oeis_a361035
