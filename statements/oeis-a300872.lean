import Mathlib

/-!
# Triangular-number quotients of the coefficients of OEIS A300871

Source: https://oeis.org/A300872
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a300872

/-- The exponential of n(n+1) times the ordinary generating series of A300871. -/
noncomputable def expMultiple (G : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.C ((n : ℚ) * ((n : ℚ) + 1)) * G) (PowerSeries.exp ℚ)

/-- A300871 starts at index one and specifies its series by a diagonal coefficient equation. -/
def isDefiningSeries (G : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff G = 0 ∧
    ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (expMultiple G n) =
        (n : ℚ) * ((n : ℚ) + 1) * PowerSeries.coeff (n - 1) (expMultiple G n)

/-- Each A300872 term, the A300871 coefficient divided by its triangular number, is integral. -/
theorem main : ∀ G : PowerSeries ℚ, isDefiningSeries G → ∀ n : ℕ, 0 < n →
    ∃ z : ℤ, PowerSeries.coeff n G / ((n * (n+1) / 2 : ℕ) : ℚ) = (z : ℚ) := by
  sorry

end OMA.S_oeis_a300872
