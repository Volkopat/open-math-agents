import Mathlib

/-!
# OEIS A263647: Numbers k such that 2^k-1 and 3^k-1 are coprime

Source: https://oeis.org/A263647
Credit: @unserus

OEIS: "Conjectured to be infinite: see the Ailon and Rudnick paper."

The terms are the `k ≥ 1` such that `2^k - 1` and `3^k - 1` are coprime (for
`k = 0` both are 0, so `k = 0` is excluded automatically; `1 ≤ k` is stated for
clarity). The subtraction is in `ℕ` and does not truncate for `k ≥ 1`. The
conjecture (Ailon–Rudnick) is that there are infinitely many such `k`.
-/

namespace OMA.S_oeis_a263647

/-- The terms of A263647. -/
def a263647Set : Set ℕ := {k | 1 ≤ k ∧ Nat.Coprime (2 ^ k - 1) (3 ^ k - 1)}

/-- A263647 is infinite. -/
theorem main : a263647Set.Infinite := by
  sorry

end OMA.S_oeis_a263647
