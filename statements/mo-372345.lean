import Mathlib

/-!
# Covering `ℝ² \ {0}` by monotone rectifiable Jordan curves and arclength-null sets

Source: https://mathoverflow.net/questions/372345
Credit: @artnoage

Let `(γ_t)_{t ∈ ℝ}` be a family of rectifiable Jordan curves in `ℝ²` covering `ℝ² \ {0}`,
monotone in the sense that for every `t < T`, the curve `γ_t` is contained in the closure of
the bounded connected component of `ℝ² \ γ_T`. For each `t ∈ ℝ`, let `E_t ⊆ γ_t` have zero
1-dimensional Hausdorff (arclength) measure, and suppose `E = ⋃ t, E_t` is Lebesgue measurable
in `ℝ²`. The question asks whether `E` must have zero 2-dimensional Lebesgue measure.
-/

namespace OMA.S_mo_372345

open MeasureTheory

/-- A parametrization `c : ℝ → ℝ²` of a rectifiable Jordan curve on `[0, 1]`: continuous on
`[0, 1]`, closed (`c 0 = c 1`), injective on `[0, 1)`, and of bounded variation on `[0, 1]`. -/
def IsRectifiableJordanCurve (c : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ContinuousOn c (Set.Icc 0 1) ∧ c 0 = c 1 ∧ Set.InjOn c (Set.Ico 0 1) ∧
    BoundedVariationOn c (Set.Icc 0 1)

/-- Whether a measurable union `E = ⋃ t, E_t` of arclength-null subsets `E_t ⊆ γ_t` along a
monotone family of rectifiable Jordan curves covering `ℝ² \ {0}` must have zero planar
Lebesgue measure. -/
theorem main :
    ∀ (γ : ℝ → ℝ → EuclideanSpace ℝ (Fin 2))
      (E : ℝ → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ t, IsRectifiableJordanCurve (γ t)) →
      (⋃ t : ℝ, γ t '' Set.Icc 0 1) = ({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ →
      (∀ T, ∃ x ∈ (γ T '' Set.Icc 0 1)ᶜ,
        Bornology.IsBounded (connectedComponentIn (γ T '' Set.Icc 0 1)ᶜ x)) →
      (∀ t T, t < T → ∀ x ∈ (γ T '' Set.Icc 0 1)ᶜ,
        Bornology.IsBounded (connectedComponentIn (γ T '' Set.Icc 0 1)ᶜ x) →
        γ t '' Set.Icc 0 1 ⊆ closure (connectedComponentIn (γ T '' Set.Icc 0 1)ᶜ x)) →
      (∀ t, E t ⊆ γ t '' Set.Icc 0 1) →
      (∀ t, Measure.hausdorffMeasure 1 (E t) = 0) →
      MeasurableSet (⋃ t : ℝ, E t) →
      volume (⋃ t : ℝ, E t) = 0 := by
  sorry

end OMA.S_mo_372345
