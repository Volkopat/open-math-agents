import Mathlib

/-!
# OEIS A390839

The product of the first n ratios of one plus a prime to the next prime gap
is an integer.

Source: https://oeis.org/A390839
Credit: @gblacher2
-/

namespace OMA.S_oeis_a390839

open scoped BigOperators

/-- The exact product before rounding. Mathlib's prime index starts at zero. -/
noncomputable def primeGapProduct (n : ℕ) : ℚ :=
  let p : ℕ → ℚ := fun k => (Nat.nth Nat.Prime k : ℚ)
  ∏ k ∈ Finset.range n, (p k + 1) / (p (k + 1) - p k)

theorem main : ∀ n : ℕ, ∃ z : ℤ, primeGapProduct n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a390839
