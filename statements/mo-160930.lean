import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OMA.S_mo_160930

/-- The proposed Euler gamma ratio bound on the strip with real part strictly
between one and two. -/
theorem main :
    ∀ s : ℂ, 1 < s.re → s.re < 2 →
      ‖Complex.Gamma s / Complex.Gamma (2 - s)‖ ≤
        Real.rpow ‖s‖ (2 * (s.re - 1)) := by
  sorry

end OMA.S_mo_160930
