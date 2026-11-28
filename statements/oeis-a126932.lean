import Mathlib

/-!
# OEIS A126932

Source: https://oeis.org/A126932 (OEIS Foundation, CC BY-SA 4.0).
R. J. Mathar's recurrence is stated from index 3, since the sequence has
offset 0 and the recurrence uses the term three positions earlier.
The sequence is defined by Paul Barry's generating function in the entry.
-/

namespace OMA.S_oeis_a126932

open PowerSeries

/-- The formal square root of `(1 + X) * (1 - 3 * X)` with constant term 1. -/
noncomputable def root : PowerSeries ℚ :=
  PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) *
    rescale (-3) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))

/-- Paul Barry's ordinary generating function for A126932. -/
noncomputable def generatingFunction : PowerSeries ℚ :=
  (root + C 3 * (1 - C 3 * X)) * (C 2 * (C 2 - C 13 * X + C 21 * X ^ 2))⁻¹

noncomputable def a (n : ℕ) : ℚ := coeff n generatingFunction

/-- The complete recurrence conjectured by R. J. Mathar in the source entry. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℚ) * a n - 11 * (n : ℚ) * a (n - 1) +
      4 * (2 * (n : ℚ) + 3) * a (n - 2) +
      21 * ((n : ℚ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a126932
