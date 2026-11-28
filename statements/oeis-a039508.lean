import Mathlib

/-!
# OEIS A039508: the `3x + 5` problem

Source: https://oeis.org/A039508
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A039508 counts the (conjectural) minimum points of the `3x + (2n+1)` problems. The entry records
the conjecture that in the `3x + 5` problem (`x ↦ x/2` if `x` is even, `3x + 5` if `x` is odd)
every positive integer eventually reaches one of `1, 5, 19, 23, 187, 347`.

Conventions:
* Positive integers `x ≥ 1`; "reaches" means some iterate equals one of the six values.
-/

namespace OMA.S_oeis_a039508

/-- The `3x + 5` map. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 5

/-- Every positive integer reaches one of `1, 5, 19, 23, 187, 347`. -/
theorem main : ∀ x : ℕ, 1 ≤ x → ∃ i : ℕ, T^[i] x ∈ ({1, 5, 19, 23, 187, 347} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a039508
