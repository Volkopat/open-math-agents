import Mathlib

/-!
# The largest exception in OEIS A390380

Emmanuel Osalotioman Osazuwa conjectures that 6563 is the largest integer
without a bounded representation as a sum of two squares minus a third.
Source: https://oeis.org/A390380
Credit: @siddsg7
-/

namespace OMA.S_oeis_a390380

/-- Integers with no such representation, including every negative integer. -/
def exceptions : Set ℤ :=
  {k | ¬ ∃ x y z : ℤ,
    x ^ 2 ≤ k ∧ y ^ 2 ≤ k ∧ z ^ 2 ≤ k ∧ x ^ 2 + y ^ 2 - z ^ 2 = k}

theorem main : IsGreatest exceptions 6563 := by
  sorry

end OMA.S_oeis_a390380
