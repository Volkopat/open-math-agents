import Mathlib

/-!
# A087214: Expansion of e.g.f.: exp(x)/(1-x^2/2)

Source: https://oeis.org/A087214
Credit: @ivillar

Offset 0, data 1, 1, 2, 4, 13, 41, 196, 862, ... a(n) is n! times the coefficient of x^n in the
e.g.f. exp(x)/(1-x^2/2), taken below as a power series over ℚ (the inverse of 1 - x^2/2 is the
power series inverse, which exists as the constant coefficient is 1).

Conjecture (R. J. Mathar, Aug 19 2014):
2*a(n) -2*a(n-1) -n*(n-1)*a(n-2) +(n-1)*(n-2)*a(n-3)=0.
It is stated for n ≥ 3 (all indices at least the offset 0).
Status: known result: Robert Israel (Apr 30 2026) verified the conjecture in the entry, using the
differential equation (-x^2 + 2*x + 2)*y(x) + (x^2 - 2)*y'(x) = 0 satisfied by the e.g.f.
-/

namespace OMA.S_oeis_a087214

/-- The e.g.f. exp(x)/(1-x^2/2). -/
noncomputable def E : PowerSeries ℚ :=
  PowerSeries.exp ℚ * (1 - (1 / 2 : ℚ) • PowerSeries.X ^ 2)⁻¹

/-- a(n) = n! * [x^n] E. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * PowerSeries.coeff n E

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * a n - 2 * a (n - 1) - (n : ℚ) * ((n : ℚ) - 1) * a (n - 2) +
      ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a087214
