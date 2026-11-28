import Mathlib

/-!
# Is it true that `{x^4 + y^3 + z^2 : x, y, z ∈ ℚ_{≥0}} = ℚ_{≥0}`?

Source: https://mathoverflow.net/questions/415268
Credit: @JeremyDevs

Formalizes the "4-3-2 Conjecture" of Zhi-Wei Sun (MathOverflow 415268, 2022): each
`r ∈ ℚ_{≥0}` can be written as `x^4 + y^3 + z^2` with `x, y, z ∈ ℚ_{≥0}`, where `ℚ_{≥0}` is the
set of all nonnegative rational numbers. The question asks whether the conjecture is true;
`main` is the conjecture (the affirmative answer, which the source conjectures).

Conventions:
* `ℚ_{≥0}` is rendered by rationals `r : ℚ` with `0 ≤ r`; the three variables are required to
  be nonnegative as in the source.
* The set equality of the title is the same statement: the inclusion `⊆` is trivial (a sum of
  nonnegative rationals is nonnegative), so only `⊇`, i.e. the conjecture as worded in the body,
  is stated.
-/

namespace OMA.S_mo_415268

/-- The 4-3-2 conjecture: every nonnegative rational is `x^4 + y^3 + z^2` with nonnegative
rational `x, y, z`. -/
theorem main :
    ∀ r : ℚ, 0 ≤ r → ∃ x y z : ℚ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ r = x ^ 4 + y ^ 3 + z ^ 2 := by
  sorry

end OMA.S_mo_415268
