import Mathlib

/-!
# OEIS A079044: negative partial sums of sin(j/π)

Source: https://oeis.org/A079044
`a n` lists the `k` such that `∑_{j=0}^{k} sin(j/π) < 0`. Conjecture (checked for `n ≤ 10^4`):
`a(n) = ⌊2 π² n⌋`.

Conventions. Offset `1`: `a n = Nat.nth P (n - 1)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a079044

open Real

/-- `∑_{j=0}^{k} sin(j/π) < 0`. -/
def P (k : ℕ) : Prop := ∑ j ∈ Finset.range (k + 1), sin (j / π) < 0

theorem main : ∀ n : ℕ, 1 ≤ n → Nat.nth P (n - 1) = ⌊2 * π ^ 2 * n⌋₊ := by
  sorry

end OMA.S_oeis_a079044
