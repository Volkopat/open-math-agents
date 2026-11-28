import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
MathOverflow 466940 asks whether two proposed probability bounds follow for
arbitrary bounded adapted real random variables. The main assertion below
records both universal bounds with their stated absolute-value assumption.
Source: https://mathoverflow.net/questions/466940

Marcus M already answered negatively on March 13, 2024 using independent
Rademacher variables. The separate complete proof gives a simpler deterministic
counterexample: thirty-two variables identically minus one on a one-point
probability space, with B = 1 and delta = 1/2. Both asserted success events
are empty. This does not refute Freedman's inequality or the nonnegative variant.
-/

open MeasureTheory

namespace OMA.S_mo_466940

def firstEvent {Ω : Type} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (F : Filtration ℕ m) (Z : ℕ → Ω → ℝ) (T : ℕ) (B δ : ℝ) : Set Ω :=
  {ω | (∑ t ∈ Finset.Icc 1 T, Z t ω) ≤
    (3 / 2 : ℝ) * (∑ t ∈ Finset.Icc 1 T, μ[Z t | F (t - 1)] ω) +
      4 * B * Real.log (2 / δ)}

def secondEvent {Ω : Type} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (F : Filtration ℕ m) (Z : ℕ → Ω → ℝ) (T : ℕ) (B δ : ℝ) : Set Ω :=
  {ω | (∑ t ∈ Finset.Icc 1 T, μ[Z t | F (t - 1)] ω) ≤
    2 * (∑ t ∈ Finset.Icc 1 T, Z t ω) + 8 * B * Real.log (2 / δ)}

def FirstClaim : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m),
    IsProbabilityMeasure μ →
    ∀ (F : Filtration ℕ m) (Z : ℕ → Ω → ℝ) (T : ℕ) (B δ : ℝ),
      Adapted F Z → 0 < B → 0 < δ → δ < 1 →
      (∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, |Z t ω| ≤ B) →
      1 - δ ≤ μ.real (firstEvent μ F Z T B δ)

def SecondClaim : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m),
    IsProbabilityMeasure μ →
    ∀ (F : Filtration ℕ m) (Z : ℕ → Ω → ℝ) (T : ℕ) (B δ : ℝ),
      Adapted F Z → 0 < B → 0 < δ → δ < 1 →
      (∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, |Z t ω| ≤ B) →
      1 - δ ≤ μ.real (secondEvent μ F Z T B δ)

theorem main : FirstClaim ∧ SecondClaim := by
  sorry

end OMA.S_mo_466940
