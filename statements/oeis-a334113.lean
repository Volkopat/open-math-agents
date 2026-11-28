import Mathlib

/-!
# OEIS A334113: positive integers not of the form 4x⁴ + y(y+1)/2 + z(z+1)/2

Source: https://oeis.org/A334113 (conjecture in COMMENTS)
Credit: @LEGZM

The sequence lists the positive numbers not of the form 4x⁴ + y(y+1)/2 + z(z+1)/2 with x, y, z
nonnegative integers. Conjecture: the sequence has only 602 terms (as listed in the b-file; the
602nd is 31737789).
-/

namespace OMA.S_oeis_a334113

/-- n is of the form 4x⁴ + y(y+1)/2 + z(z+1)/2 with x, y, z ≥ 0. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = 4 * x ^ 4 + y * (y + 1) / 2 + z * (z + 1) / 2

theorem main : {n : ℕ | 0 < n ∧ ¬ IsRepresentable n}.ncard = 602 := by
  sorry

end OMA.S_oeis_a334113
