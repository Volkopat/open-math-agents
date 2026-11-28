import Mathlib

/-!
# Infinitely many members of OEIS A111205

Source: https://oeis.org/A111205
Credit: @etaubman

The strict inequalities put k between consecutive squares. Their difference is
2 * r + 1, so the gcd below is exactly the one in the OEIS definition.
-/

namespace OMA.S_oeis_a111205

/-- Nonsquare composite numbers sharing a factor with the gap between their surrounding squares. -/
def terms : Set ℕ :=
  {k | 1 < k ∧ ¬ k.Prime ∧ ∃ r : ℕ,
    r ^ 2 < k ∧ k < (r + 1) ^ 2 ∧ 1 < Nat.gcd k (2 * r + 1)}

theorem main : terms.Infinite := by
  sorry

end OMA.S_oeis_a111205
