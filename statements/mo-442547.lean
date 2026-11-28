import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# MathOverflow 442547: a proposed integral inequality

Source: https://mathoverflow.net/questions/442547/question-on-an-integral-inequality
Question by newbie, 12 March 2023.

This states the displayed implication using a probability measure, arbitrary
real r > 1, measurable real functions, an integrable envelope for f alone,
and the stated strict L1 bound. The right side is the integral of the product.
No pointwise envelope hypothesis is added for g.
-/

namespace OMA.S_mo_442547

def claim : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (r : ℝ) (f g F : Ω → ℝ),
    1 < r → Measurable f → Measurable g → Measurable F →
    (∀ x, |f x| ≤ F x) → Integrable F Q →
    (∫ x, |f x - g x| ∂Q) < 2 * (∫ x, F x ∂Q) →
    (∫ x, |f x - g x| ^ r ∂Q) ≤
      ∫ x, |f x - g x| * (2 * F x) ^ (r - 1) ∂Q

theorem main : claim := by
  sorry

end OMA.S_mo_442547
