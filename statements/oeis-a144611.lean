import Mathlib

/-!
# The logarithmic formula proposed for OEIS A144611

Source: https://oeis.org/A144611
Credit: @etaubman

Michel Dekking gives the mechanical word of slope 2 - sqrt(2) and intercept
zero in the source entry. The sequence starts at index 0. The conjecture
compares successive integer floors, so all differences below are in ℤ.
-/

namespace OMA.S_oeis_a144611

noncomputable def slopeFloor (n : ℕ) : ℤ := ⌊(n : ℝ) * (2 - Real.sqrt 2)⌋

noncomputable def logFloor (n : ℕ) : ℤ := ⌊(n : ℝ) * Real.log 3 / Real.log 2⌋

def conjecture : Prop :=
  ∀ n : ℕ, slopeFloor (n + 1) - slopeFloor n = logFloor (n + 1) - logFloor n - 1

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a144611
