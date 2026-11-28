import Mathlib

/-!
# Integer coefficients and triangular divisibility of OEIS A300617

Source: https://oeis.org/A300617
Credit: @HBreitkreutz
-/

namespace OMA.S_oeis_a300617

/-- The formal exponential of the scalar multiple `n * G`. -/
noncomputable def expMultiple (G : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.C (n : ℚ) * G) (PowerSeries.exp ℚ)

/-- The zero-constant ordinary generating series specified by A300617. -/
def isDefiningSeries (G : PowerSeries ℚ) : Prop :=
  PowerSeries.constantCoeff G = 0 ∧
    ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (expMultiple G n) =
        (n : ℚ) ^ 2 * PowerSeries.coeff (n - 1) (expMultiple G n)

/-- The coefficient at each positive index is an integer divisible by the
corresponding triangular number. -/
theorem main : ∀ G : PowerSeries ℚ, isDefiningSeries G → ∀ n : ℕ, 0 < n →
    ∃ a : ℤ, PowerSeries.coeff n G = (a : ℚ) ∧
      ((n * (n + 1) / 2 : ℕ) : ℤ) ∣ a := by
  sorry

end OMA.S_oeis_a300617
