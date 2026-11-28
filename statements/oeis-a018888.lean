import Mathlib

/-!
# OEIS A018888: numbers that are not sums of seven nonnegative cubes

Source: https://oeis.org/A018888
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The old name of the entry gives the conjectured list of numbers that need `8` or `9` positive
cubes: `15, 22, 23, 50, 114, 167, 175, 186, 212, 231, 238, 239, 303, 364, 420, 428, 454`
(Siksek has since shown the list is complete). `main` states that these are exactly the natural
numbers that are not sums of seven nonnegative cubes.
-/

namespace OMA.S_oeis_a018888

/-- `n` is a sum of seven nonnegative cubes. -/
def SumSevenCubes (n : ℕ) : Prop := ∃ m : Fin 7 → ℕ, n = ∑ i, m i ^ 3

/-- The exceptions to seven cubes. -/
theorem main : {n : ℕ | ¬ SumSevenCubes n} =
    {15, 22, 23, 50, 114, 167, 175, 186, 212, 231, 238, 239, 303, 364, 420, 428, 454} := by
  sorry

end OMA.S_oeis_a018888
