import Mathlib

/-!
# A distribution on `{x + y + z = 3/2} ∩ [0,1]³` with uniform marginals

Source: https://mathoverflow.net/questions/481234
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 481234, Iosif Pinelis, Oct 2024): does there exist a probability
distribution over the set `{(x, y, z) ∈ [0,1]³ : x + y + z = 3/2}` whose projection on each of
the three coordinate axes is the uniform distribution over `[0, 1]`? The question was edited to
say it "has now been answered, quite elementarily, by Ilya Bogdanov" (in the affirmative, via the
answer to the linked question 481225). This file states the affirmative answer.

Modelling choices:
* Points of `ℝ³` are triples `ℝ × ℝ × ℝ`; a "probability distribution over the set" is a
  probability measure on `ℝ × ℝ × ℝ` giving full measure to that set.
* "Projection on each coordinate axis is uniform on `[0, 1]`" is: the push-forward under each of
  the three coordinate maps is Lebesgue measure restricted to `[0, 1]`.
-/

namespace OMA.S_mo_481234

open MeasureTheory

/-- The set `{(x, y, z) ∈ [0,1]³ : x + y + z = 3/2}`. -/
def S : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    p.1 + p.2.1 + p.2.2 = 3 / 2}

/-- **MathOverflow 481234.** There is a probability distribution on `S` all of whose
one-dimensional coordinate marginals are uniform on `[0, 1]`. -/
theorem main :
    ∃ ν : Measure (ℝ × ℝ × ℝ), IsProbabilityMeasure ν ∧ ν Sᶜ = 0 ∧
      ν.map (fun p => p.1) = volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      ν.map (fun p => p.2.1) = volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      ν.map (fun p => p.2.2) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  sorry

end OMA.S_mo_481234
