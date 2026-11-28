import Mathlib

/-!
# A joint law of `α` and `β` from the laws of `α`, `β` and `α / β`

Source: https://mathoverflow.net/questions/12853
Credit: @koolkao

Question (MathOverflow 12853, 2010; CC BY-SA 2.5). Given probability density functions of random
variables `α`, `β` and `α / β`, we would like to devise a joint distribution of `α` and `β`. The
solution need not be unique; we would like to find one.

We state the question in the reading made explicit by its only answer: is it always possible to
find a joint distribution of `(α, β)` for any prescribed densities of `α`, `β` and `α / β`?
`main` states that the answer is yes. A disproof is a choice of three densities for which no
joint law exists.

Translation choices:
* a probability density on `ℝ` is a measurable `f : ℝ → ℝ≥0∞` with `∫⁻ f = 1` (Lebesgue
  measure); the law with density `f` is `volume.withDensity f`;
* a joint distribution of `(α, β)` is a probability measure `μ` on `ℝ × ℝ`; its marginals are the
  pushforwards under `Prod.fst` and `Prod.snd`, and the law of `α / β` is the pushforward under
  `p ↦ p.1 / p.2` (Lean's real division, with `x / 0 = 0`; this convention plays no role when the
  law of `β` has a density, since then `β ≠ 0` almost surely);
* "find a joint distribution" means that such a `μ` exists with all three pushforwards equal to
  the prescribed laws.
-/

namespace OMA.S_mo_12853

open MeasureTheory
open scoped ENNReal

/-- `f` is a probability density on `ℝ`. -/
def IsDensity (f : ℝ → ℝ≥0∞) : Prop :=
  Measurable f ∧ ∫⁻ x, f x = 1

/-- For any prescribed densities of `α`, `β` and `α / β` there is a joint law of `(α, β)` with
these marginals and this law of the ratio. -/
theorem main :
    ∀ fα fβ fr : ℝ → ℝ≥0∞, IsDensity fα → IsDensity fβ → IsDensity fr →
      ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧
        μ.map Prod.fst = volume.withDensity fα ∧
        μ.map Prod.snd = volume.withDensity fβ ∧
        μ.map (fun p => p.1 / p.2) = volume.withDensity fr := by
  sorry

end OMA.S_mo_12853
