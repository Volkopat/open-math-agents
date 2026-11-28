import Mathlib

/-!
# Least positive solutions for OEIS A197521 and A197383

Source: https://oeis.org/A197521
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a197521

def sineRoots : Set ℝ :=
  {t | 0 < t ∧ Real.sin (Real.pi*t/6) = Real.sin (Real.pi*t/3)^2}

def cosineRoots : Set ℝ :=
  {x | 0 < x ∧ Real.cos (Real.pi*x/2) = Real.cos (Real.pi*x/3)^2}

theorem main : ∃ x t : ℝ, IsLeast cosineRoots x ∧ IsLeast sineRoots t ∧ x = 3+t := by
  sorry

end OMA.S_oeis_a197521
