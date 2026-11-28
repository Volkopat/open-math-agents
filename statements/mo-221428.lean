import Mathlib

/-!
# A generalized ballot theorem for independent identically distributed increments

Source: https://mathoverflow.net/questions/221428 (Vladimir, CC BY-SA 3.0).
Credit: @connoranderson

The first n increments have indices 0 through n−1. Subtracting the threshold ν from each
increment makes a negative partial sum equivalent to the original strict inequality.
An eventually positive probability sequence has the form exp(−γn+o(n)) exactly when
its log divided by n tends to −γ.
-/

namespace OMA.S_mo_221428

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def below {Ω : Type*} (X : ℕ → Ω → ℝ) (ν : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∑ j ∈ Finset.range k, (X j ω-ν)) < 0}

def staysBelow {Ω : Type*} (X : ℕ → Ω → ℝ) (ν : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k : ℕ, 0 < k → k ≤ n → ω ∈ below X ν k}

def rate (f : ℕ → ℝ) (γ : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0<f n) ∧ Tendsto (fun n : ℕ => Real.log (f n)/(n:ℝ)) atTop (𝓝 (-γ))

theorem main : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (law : Measure ℝ) [IsProbabilityMeasure law] (ν γ : ℝ),
    iIndepFun X P → (∀ j, HasLaw (X j) law P) → Integrable (X 0) P →
    ν ≤ ∫ ω, X 0 ω ∂P → 0 < γ →
    rate (fun n => P.real (below X ν n)) γ → rate (fun n => P.real (staysBelow X ν n)) γ := by
  sorry

end OMA.S_mo_221428
