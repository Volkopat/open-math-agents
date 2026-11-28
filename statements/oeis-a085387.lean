import Mathlib

/-!
# OEIS A085387: e.g.f. exp(x)*cosh(x+x^2/2)

Source: https://oeis.org/A085387
Credit: @adamghaida (agent: grok-bot)

A085387 is 1, 1, 2, 7, 23, 71, 242, 925, ... (offset 0), the sequence with exponential generating
function `exp(x) * cosh(x + x^2/2)`.

Conjecture (R. J. Mathar, Nov 24 2012):
`a(n) - 3*a(n-1) + 2*a(n-2) + (-2*n+3)*a(n-3) - (n-3)^2*a(n-4) + (n-3)*(n-4)*a(n-5) = 0`.

Formalization notes:
* `a n = n! * [x^n] (exp(x) * cosh(x + x^2/2))`, computed in `ℚ` with formal power series;
  `cosh z` is written as `(exp z + exp (-z))/2` and `exp (±(x + x^2/2))` is the substitution of
  `±(x + x^2/2)` (constant coefficient 0) into the exponential series.
* The recurrence involves `a(n-5)`, so it is stated for every `n ≥ 5`.
-/

namespace OMA.S_oeis_a085387

open PowerSeries

/-- The formal power series `x + x^2/2`. -/
noncomputable def u : ℚ⟦X⟧ := X + C (1 / 2 : ℚ) * X ^ 2

/-- The exponential generating function `exp(x) * cosh(x + x^2/2)`. -/
noncomputable def egf : ℚ⟦X⟧ :=
  exp ℚ * (C (1 / 2 : ℚ) * ((exp ℚ).subst u + (exp ℚ).subst (-u)))

/-- `a n = n! * [x^n] egf`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n egf

theorem main : ∀ n : ℕ, 5 ≤ n →
    a n - 3 * a (n - 1) + 2 * a (n - 2) + (-2 * (n : ℚ) + 3) * a (n - 3)
      - ((n : ℚ) - 3) ^ 2 * a (n - 4) + ((n : ℚ) - 3) * ((n : ℚ) - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a085387
