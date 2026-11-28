import Mathlib

/-!
# OEIS A027870: zero digits of powers of two

Source: https://oeis.org/A027870
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of zero digits in the decimal expansion of `2ⁿ`. Conjecture (OEIS entry):
every value `x = 0, 1, 2, …` occurs only finitely many times in this sequence.
-/

namespace OMA.S_oeis_a027870

/-- Number of zero decimal digits of `2ⁿ`. -/
def a (n : ℕ) : ℕ := ((Nat.digits 10 (2 ^ n)).filter (· = 0)).length

/-- Each value is taken only finitely often. -/
theorem main : ∀ x : ℕ, {n : ℕ | a n = x}.Finite := by
  sorry

end OMA.S_oeis_a027870
