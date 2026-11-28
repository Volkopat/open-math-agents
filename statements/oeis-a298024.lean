import Mathlib

/-!
# OEIS A298024: Expansion of (x^4+3*x^3+6*x^2+3*x+1)/((1-x)*(1-x^3))

Source: https://oeis.org/A298024
Credit: @unserus

OEIS: "a(n) = a(n-1) + a(n-3) - a(n-4) for n>4. (Conjectured, correctly, by Colin Barker,
Jan 22 2018.)"

The sequence is defined as the coefficients of the rational generating function
`(1 + 3x + 6x^2 + 3x^3 + x^4) / ((1 - x)(1 - x^3))`, computed here in `ℚ⟦X⟧` (the denominator has
constant term 1, so it is invertible; the coefficients are the integers 1, 4, 10, 14, 18, 24, ...).
The statement is Barker's recurrence for `n > 4`.
-/

namespace OMA.S_oeis_a298024

open PowerSeries

/-- The generating function `(1 + 3x + 6x^2 + 3x^3 + x^4) / ((1 - x)(1 - x^3))` over `ℚ`. -/
noncomputable def G : PowerSeries ℚ :=
  (1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4) * ((1 - X) * (1 - X ^ 3))⁻¹

/-- A298024(n): the coefficient of `x^n` in `G`. -/
noncomputable def a (n : ℕ) : ℚ := coeff n G

/-- Barker's recurrence: `a(n) = a(n-1) + a(n-3) - a(n-4)` for `n > 4`. -/
theorem main : ∀ n : ℕ, 4 < n → a n = a (n - 1) + a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a298024
