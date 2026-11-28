import Mathlib

/-!
# Random disks of area π, π/2, π/3, … cover a disk of area π almost surely

Source: https://mathoverflow.net/questions/458793
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 458793, Dan, Nov 2023): on a "bottom" disk of area `π`, place "top"
disks of area `π, π/2, π/3, …` such that the centre of each top disk is an independent uniformly
random point on the bottom disk. Will the bottom disk be completely covered by the top disks with
probability `1`? (The asker has arguments for bottom area `< π` (yes) and `> π` (no); the boundary
case is the question.) An answer (2026) says yes, with probability `1` the closed bottom disk is
covered, using Theorem 2.1 of a preprint of Yechi Zhou for the interior and Shepp's theorem for
random arcs for the rim; it takes the top disks open. This file states that affirmative answer.

Modelling choices:
* The plane is `EuclideanSpace ℝ (Fin 2)`. The bottom disk is the closed unit disk `D` (area `π`);
  the `n`-th top disk (`n = 0, 1, 2, …` standing for `1, 2, 3, …`) is the open disk of radius
  `1 / √(n + 1)` (area `π / (n + 1)`) centred at `X n`. Covering the closed disk by open disks is
  the strongest reading, and is the one the answer proves.
* The centres are measurable, mutually independent (`iIndepFun`) and uniform on `D`, i.e. each has
  law `cond volume D` (Lebesgue measure restricted to `D` and normalized).
* "With probability `1`" is `∀ᵐ ω ∂μ`.
-/

namespace OMA.S_mo_458793

open MeasureTheory ProbabilityTheory

/-- The bottom disk: the closed unit disk, of area `π`. -/
def D : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 1

/-- **MathOverflow 458793.** Almost surely, the open disks of radius `1 / √(n + 1)` around
independent uniform points of the unit disk cover the closed unit disk. -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → EuclideanSpace ℝ (Fin 2)),
      (∀ n, Measurable (X n)) →
      iIndepFun X μ →
      (∀ n, μ.map (X n) = cond volume D) →
      ∀ᵐ ω ∂μ, D ⊆ ⋃ n : ℕ, Metric.ball (X n ω) (1 / Real.sqrt ((n : ℝ) + 1)) := by
  sorry

end OMA.S_mo_458793
