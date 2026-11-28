import Mathlib

/-!
# A258902: Expansion of e.g.f. Series_Reversion(x - x^2/2 - x^3/3).

Source: https://oeis.org/A258902
Credit: @AngelHS12

Conjecture (R. J. Mathar, Jun 07 2016, formula section of the entry):
`19*a(n) + 21*(-2*n+3)*a(n-1) - 4*(3*n-5)*(3*n-7)*a(n-2) = 0`.

Conventions:
* Offset 1, as in the entry (data 1, 1, 5, 35, 355, 4585, ...): `a(n) = n! [x^n] A(x)`, where the
  e.g.f. `A` is the series reversion of `x - x^2/2 - x^3/3`, i.e. the power series with `A(0) = 0`
  and `A - A^2/2 - A^3/3 = x` (equivalently `A(x - x^2/2 - x^3/3) = x`, as the entry's example
  says). Such an `A` is unique, being determined coefficient by coefficient; `main` quantifies
  over every such `A`.
* The source gives no range for the recurrence. It is stated for every `n ≥ 3`: the indices at
  which `a(n)`, `a(n-1)` and `a(n-2)` all belong to the sequence (offset 1).
-/

namespace OMA.S_oeis_a258902

open PowerSeries

/-- The e.g.f. coefficients of `A`: `a(n) = n! * [x^n] A`. -/
noncomputable def a (A : PowerSeries ℚ) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n A

/-- Mathar's conjectured recurrence for A258902. -/
theorem main : ∀ A : PowerSeries ℚ, constantCoeff A = 0 →
    A - C (1 / 2 : ℚ) * A ^ 2 - C (1 / 3 : ℚ) * A ^ 3 = X →
    ∀ n : ℕ, 3 ≤ n →
      19 * a A n + 21 * (-2 * (n : ℚ) + 3) * a A (n - 1)
        - 4 * (3 * (n : ℚ) - 5) * (3 * (n : ℚ) - 7) * a A (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a258902
