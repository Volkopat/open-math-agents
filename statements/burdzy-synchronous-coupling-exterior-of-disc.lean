import Mathlib
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Synchronous reflection outside a closed disc

Krzysztof Burdzy, "My favorite open problems", Problem 5(ii).
https://sites.math.washington.edu/~burdzy/open_mathjax.php
Credit: @pmaster

The plane is identified with the complex numbers. Normal reflection is
specified by the Skorokhod equation. The measure in the equation is the
Stieltjes measure of a continuous nondecreasing boundary regulator starting
at zero. On the circle the inward unit normal of the exterior is (z-c)/r.
The pathwise formulation permits any realization of the synchronous coupling.
-/

namespace OMA.S_burdzy_synchronous_coupling_exterior_of_disc

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

def Reflects (c : ℂ) (r : ℝ) (start : ℂ) (driver path : ℝ≥0 → ℂ) : Prop :=
  Continuous path ∧ path 0 = start ∧ (∀ t, r ≤ ‖path t - c‖) ∧
    ∃ localTime : Measure ℝ≥0,
      (∀ t : ℝ≥0, localTime {t} = 0) ∧
      (∀ t : ℝ≥0, localTime (Icc 0 t) < ∞) ∧
      (∀ᵐ s ∂localTime, ‖path s - c‖ = r) ∧
      ∀ t, path t = start + driver t +
        ∫ s in Icc 0 t, ((path s - c) / (r : ℂ)) ∂localTime

theorem main : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U V : ℝ≥0 → Ω → ℝ) (X Y : ℝ≥0 → Ω → ℂ)
    (c : ℂ) (r : ℝ) (x y : ℂ),
    0 < r → r ≤ ‖x - c‖ → r ≤ ‖y - c‖ → x ≠ y →
    IsBrownianReal U P → IsBrownianReal V P →
    IndepFun (fun ω t => U t ω) (fun ω t => V t ω) P →
    (∀ t, AEMeasurable (X t) P ∧ AEMeasurable (Y t) P) →
    (∀ᵐ ω ∂P,
      let driver := fun t => Complex.mk (U t ω) (V t ω)
      Reflects c r x driver (fun t => X t ω) ∧
      Reflects c r y driver (fun t => Y t ω)) →
    0 < P {ω | ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ≥0, ∃ t ≥ T, ε ≤ dist (X t ω) (Y t ω)} := by
  sorry

end OMA.S_burdzy_synchronous_coupling_exterior_of_disc
