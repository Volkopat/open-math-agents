import Mathlib

/-!
# Integer coefficients and divisibility by the index in OEIS A300591

Source: https://oeis.org/A300591
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a300591

/-- The formal exponential of the scalar multiple n² times G. -/
noncomputable def expMultiple (G : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.C ((n : ℚ) ^ 2) * G) (PowerSeries.exp ℚ)

/-- The zero-constant ordinary generating series specified by A300591. -/
def isDefiningSeries (G : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff G = 0 ∧
    ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (expMultiple G n) =
        (n : ℚ) ^ 2 * PowerSeries.coeff (n - 1) (expMultiple G n)

/-- At every positive index the coefficient is an integer divisible by that index. -/
theorem main : ∀ G : PowerSeries ℚ, isDefiningSeries G → ∀ n : ℕ, 0 < n →
    ∃ a : ℤ, PowerSeries.coeff n G = (a : ℚ) ∧ (n : ℤ) ∣ a := by
  sorry

end OMA.S_oeis_a300591
