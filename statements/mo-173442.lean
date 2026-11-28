import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace OMA.S_mo_173442

/-- The decimal digit of the square root of two at fractional position n + 1. -/
noncomputable def decimalDigit (n : ℕ) : ℤ :=
  ⌊(10 : ℝ) ^ (n + 1) * Real.sqrt 2⌋ % 10

/-- The square root of two written in decimal, with the same digits
read as a base-eleven expansion. -/
noncomputable def thetaEleven : ℝ :=
  1 + ∑' n : ℕ, (decimalDigit n : ℝ) / (11 : ℝ) ^ (n + 1)

/-- Is the real number obtained by this change of base transcendental? -/
theorem main : Transcendental ℚ thetaEleven := by
  sorry

end OMA.S_mo_173442
