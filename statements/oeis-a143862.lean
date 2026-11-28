import Mathlib

/-!
# OEIS A143862

Source: https://oeis.org/A143862.
The sequence uses Paul D. Hanna's independent divisor-sum formula, recorded
in the entry on April 25, 2018. Joerg Arndt's January 4, 2024 conjecture is
the generating-function identity. The positive-index sum is written with a
zero summand at index 0. Sums of power series use the coefficientwise topology.
-/

namespace OMA.S_oeis_a143862

open PowerSeries
open scoped BigOperators PowerSeries.WithPiTopology

/-- The divisor-sum expression for the composition count in A143862. -/
def a (m : ℕ) : ℕ :=
  if m = 0 then 1 else ∑ d ∈ m.divisors, (m / d - 1).choose (d - 1)

noncomputable def generatingFunction : PowerSeries ℚ :=
  PowerSeries.mk fun m => (a m : ℚ)

/-- The summands in Arndt's generating function, indexed by positive d. -/
noncomputable def summand (d : ℕ) : PowerSeries ℚ :=
  if d = 0 then 0 else (X ^ d * (1 - X ^ d)⁻¹) ^ d

/-- Arndt's conjectured ordinary generating function, with the sum over d ≥ 1. -/
theorem main : generatingFunction = 1 + ∑' d : ℕ, summand d := by
  sorry

end OMA.S_oeis_a143862
