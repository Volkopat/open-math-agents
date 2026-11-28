import Mathlib

/-!
# OEIS A085785: x ↦ x⌈x⌉ starting at (2n+1)/4

Source: https://oeis.org/A085785
Start at `(2n+1)/4` and iterate the map `x ↦ x · ⌈x⌉`; the sequence gives the number of steps
until the denominator drops. The entry conjectures that the denominator always does drop.

Conventions. `n ≥ 1`; "the denominator drops" means that some iterate has (reduced)
denominator less than `4`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a085785

/-- The map `x ↦ x · ⌈x⌉` on `ℚ`. -/
def f (x : ℚ) : ℚ := x * ⌈x⌉

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, (f^[m] ((2 * n + 1 : ℚ) / 4)).den < 4 := by
  sorry

end OMA.S_oeis_a085785
