import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weak (1,1) constants for the centered Euclidean ball maximal function
Source: https://mathoverflow.net/questions/334162 (Rowan, with an answer by Yuval Peres).
Credit: @Rob1Ham

We use centered Euclidean balls, the convention of the Euclidean estimates
discussed in the answers. The question asks about uniform and polynomial
growth. We state both proposed bounds. An affirmative uniform bound would
give the optimal order up to constants since the weak constant is at least one.
-/

namespace OMA.S_mo_334162

open MeasureTheory Metric

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The strict superlevel set, written using a witnessing positive radius. -/
def superlevel {d : ℕ} (f : Space d → ℝ) (t : ℝ) : Set (Space d) :=
  {x | ∃ r : ℝ, 0 < r ∧
    t * (volume (ball x r)).toReal < ∫ y in ball x r, |f y|}

/-- C is an admissible weak (1,1) constant in dimension d. -/
def weakBound (d : ℕ) (C : ℝ) : Prop :=
  ∀ (f : Space d → ℝ), Integrable f volume → ∀ t : ℝ, 0 < t →
    volume (superlevel f t) ≤ ENNReal.ofReal (C / t * ∫ x, |f x|)

theorem main :
    (∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → weakBound d C) ∧
    (∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ d : ℕ, 0 < d → weakBound d (A * (d : ℝ) ^ k)) := by
  sorry

end OMA.S_mo_334162
