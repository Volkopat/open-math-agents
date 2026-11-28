import Mathlib

/-!
# A046040: Numbers that are the sum of 6 but no fewer positive cubes

Source: https://oeis.org/A046040
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (McCurley):
There are exactly 3922 positive integers that are the sum of 6 positive cubes and no fewer,
of which the largest is a(3922) = 1290740.
-/

namespace OMA.S_oeis_a046040

/-- n is a sum of k positive cubes. -/
def IsSumOfPosCubes (k n : ℕ) : Prop :=
  ∃ f : Fin k → ℕ, (∀ i, 0 < f i) ∧ ∑ i, (f i) ^ 3 = n

/-- The set of natural numbers that are a sum of 6 positive cubes and no fewer. -/
def reqSixCubes : Set ℕ :=
  {n : ℕ | IsSumOfPosCubes 6 n ∧ ∀ k < 6, ¬ IsSumOfPosCubes k n}

/-- Conjecture: reqSixCubes is finite of cardinality 3922 with maximum element 1290740. -/
theorem main :
    reqSixCubes.Finite ∧
      reqSixCubes.ncard = 3922 ∧
      1290740 ∈ reqSixCubes ∧
      ∀ n ∈ reqSixCubes, n ≤ 1290740 := by
  sorry

end OMA.S_oeis_a046040
