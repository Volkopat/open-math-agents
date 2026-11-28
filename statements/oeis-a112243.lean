import Mathlib

/-!
# A112243: Expansion of exp(x*(1+x)/(1-2*x)).

Source: https://oeis.org/A112243 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A112243 (Paul Barry, Aug 29 2005), offset 0, e.g.f. exp(x*(1+x)/(1-2*x)), data 1, 1, 7, 55,
577, 7441, ... Formula section, verbatim:
Conjecture: a(n) +(-4*n+3)*a(n-1) +2*(n-1)*(2*n-5)*a(n-2) +2*(n-1)*(n-2)*a(n-3)=0.
- R. J. Mathar, Feb 20 2015

Formalization notes:
* "Expansion" of an exponential generating function: a(n) = n! * [x^n] E(x), where
  E = exp(f) with f = x*(1+x)/(1-2*x) in the formal power series ring over the rationals.
  E is `(PowerSeries.exp ℚ).subst f`, Mathlib's substitution of f (constant term 0) into the
  exponential series, and 1/(1-2x) is the power series inverse of 1 - 2x.
* The values a(n) are rationals in this encoding (they are integers in the entry).
* The recurrence carries no range in the entry; it is stated for every n >= 3, the values of n
  for which all of a(n), ..., a(n-3) are terms of the sequence.
* Controls: the definition gives 1, 1, 7, 55, 577, 7441 for n = 0..5, matching the entry's data.
-/

namespace OMA.S_oeis_a112243

open PowerSeries

/-- The inner series f(x) = x*(1+x)/(1-2*x). -/
noncomputable def f : ℚ⟦X⟧ := (X + X ^ 2) * (1 - 2 * X)⁻¹

/-- The exponential generating function exp(x*(1+x)/(1-2*x)). -/
noncomputable def E : ℚ⟦X⟧ := (exp ℚ).subst f

/-- A112243(n) = n! * [x^n] exp(x*(1+x)/(1-2*x)). -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n E

/-- Mathar's conjectured recurrence for OEIS A112243. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + (-4 * (n : ℚ) + 3) * a (n - 1) + 2 * ((n : ℚ) - 1) * (2 * n - 5) * a (n - 2) +
      2 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a112243
