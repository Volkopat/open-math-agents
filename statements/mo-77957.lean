import Mathlib

open MeasureTheory

namespace OMA.S_mo_77957

/-- The Stieltjes function in the first variable at a fixed second variable. -/
def stieltjesSlice (g : ℝ → ℝ → ℝ) (hg : Continuous (Function.uncurry g))
    (hmono : ∀ x : ℝ, Monotone (fun t => g t x)) (x : ℝ) :
    StieltjesFunction ℝ where
  toFun := fun t => g t x
  mono' := hmono x
  right_continuous' := fun _ =>
    (hg.comp (continuous_id.prodMk continuous_const)).continuousWithinAt

/-- The derivative in the second variable exists almost everywhere for
the iterated Lebesgue and Stieltjes measure in the question. -/
theorem main :
    ∀ (f g : ℝ → ℝ → ℝ), Continuous (Function.uncurry f) →
      ∀ (hg : Continuous (Function.uncurry g)),
        (∃ K : NNReal, ∀ t : ℝ, LipschitzWith K (f t)) →
        (∃ K : NNReal, ∀ t : ℝ, LipschitzWith K (g t)) →
        (∀ x : ℝ, Monotone (fun t => f t x)) →
        ∀ (hmono : ∀ x : ℝ, Monotone (fun t => g t x)),
          ∀ᵐ x ∂(volume : Measure ℝ),
            ∀ᵐ t ∂(stieltjesSlice g hg hmono x).measure, DifferentiableAt ℝ (f t) x := by
  sorry

end OMA.S_mo_77957
