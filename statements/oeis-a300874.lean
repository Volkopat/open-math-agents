import Mathlib

/-!
# Integer coefficients of OEIS A300874

Source: https://oeis.org/A300874
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a300874

/-- The formal exponential of the scalar multiple n(n+1) times G. -/
noncomputable def expMultiple (G : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.C ((n : ℚ) * ((n : ℚ) + 1)) * G) (PowerSeries.exp ℚ)

/-- The zero-constant ordinary generating series specified by A300874. -/
def isDefiningSeries (G : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff G = 0 ∧
    ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (expMultiple G n) =
        2 * (n : ℚ) * PowerSeries.coeff (n - 1) (expMultiple G n)

/-- At every positive index the ordinary coefficient is an integer. -/
theorem main : ∀ G : PowerSeries ℚ, isDefiningSeries G → ∀ n : ℕ, 0 < n →
    ∃ a : ℤ, PowerSeries.coeff n G = (a : ℚ) := by
  sorry

end OMA.S_oeis_a300874
