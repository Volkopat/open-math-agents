import Mathlib

/-!
# A048820: Fixed points of Minkowski's question mark function

Source: https://oeis.org/A048820
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Gayfulin and Shulga, Conjecture 1):
Minkowski's question mark function ?(x) has exactly five fixed points on [0, 1]
(or four modulo 1).

Conventions:
Minkowski's question mark function is uniquely characterized on [0, 1] as the continuous
function f : ℝ → ℝ satisfying f(0) = 0, f(1) = 1, f(1 - x) = 1 - f(x), and
f(x / (1 + x)) = f(x) / 2 for all x ∈ [0, 1].
-/

namespace OMA.S_oeis_a048820

/-- Characterization of Minkowski's question mark function on [0, 1]. -/
def IsMinkowskiQuestionMark (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Icc 0 1) ∧
  f 0 = 0 ∧
  f 1 = 1 ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) ∧
  (∀ x ∈ Set.Icc (0 : ℝ) 1, f (x / (1 + x)) = f x / 2)

/-- Conjecture: Minkowski's question mark function has exactly 5 fixed points in [0, 1]. -/
theorem main :
    ∀ f : ℝ → ℝ, IsMinkowskiQuestionMark f →
      {x ∈ Set.Icc (0 : ℝ) 1 | f x = x}.Finite ∧
      {x ∈ Set.Icc (0 : ℝ) 1 | f x = x}.ncard = 5 := by
  sorry

end OMA.S_oeis_a048820
