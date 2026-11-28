import Mathlib

open scoped FourierTransform

namespace OMA.S_mo_360993

/-- At every real frequency, the Fourier transform of the even function
with values exp of minus the absolute power divided by the squared
exponent is decreasing in the exponent on the indicated interval. -/
theorem main :
    ∀ frequency : ℝ,
      AntitoneOn
        (fun a : ℝ =>
          (𝓕 (fun x : ℝ => ((Real.exp (-(|x| ^ a)) / a ^ 2 : ℝ) : ℂ)) frequency).re)
        (Set.Ioo 0 2) := by
  sorry

end OMA.S_mo_360993
