import Mathlib

/-!
# Vanishing exponential sums of fractional parts of polynomials

Source: Borys Kuca, MathOverflow 463783 (2024, CC BY-SA 4.0).
https://mathoverflow.net/questions/463783/vanishing-exponential-sums-of-fractional-parts-of-polynomials

We use the equivalent unit-circle formulation given by the author. At
`z = exp(2πiα/k)`, raising `z` to the least nonnegative residue of
`p(i)` gives the original summand. Every unit complex number occurs this
way, and `z ^ k = 1` is equivalent to `α` being an integer.
-/

namespace OMA.S_mo_463783

theorem main : ∀ (p : Polynomial ℤ) (k : ℕ), 0 < k →
    ∀ z : ℂ, ‖z‖ = 1 →
    (∑ j ∈ Finset.range k, z ^ (p.eval ((j : ℤ) + 1) % (k : ℤ)).toNat) = 0 →
    z ^ k = 1 := by
  sorry

end OMA.S_mo_463783

