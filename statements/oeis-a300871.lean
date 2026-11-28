import Mathlib

/-!
# Integer coefficients and triangular-number divisibility in OEIS A300871

Source: https://oeis.org/A300871
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a300871

/-- The formal exponential of the scalar multiple n(n+1) times G. -/
noncomputable def expMultiple (G : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.C ((n : ℚ) * ((n : ℚ) + 1)) * G) (PowerSeries.exp ℚ)

/-- The zero-constant ordinary generating series specified by A300871. -/
def isDefiningSeries (G : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff G = 0 ∧
    ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (expMultiple G n) =
        (n : ℚ) * ((n : ℚ) + 1) * PowerSeries.coeff (n - 1) (expMultiple G n)

/-- At every positive index the coefficient is an integer divisible by the corresponding triangular number. -/
theorem main : ∀ G : PowerSeries ℚ, isDefiningSeries G → ∀ n : ℕ, 0 < n →
    ∃ a : ℤ, PowerSeries.coeff n G = (a : ℚ) ∧ ((n * (n+1) / 2 : ℕ) : ℤ) ∣ a := by
  sorry

end OMA.S_oeis_a300871
