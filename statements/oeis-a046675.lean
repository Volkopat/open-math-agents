import Mathlib

/-!
# OEIS A046675: signs of the coefficients of `∏_p (1 - x^p)`

Source: https://oeis.org/A046675
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the coefficient of `xⁿ` in `∏_{p prime} (1 - x^p)`. Conjecture (OEIS entry):
`(-1)ⁿ a(n) ≥ 0` for all `n ≥ 50` (equivalently `A024939(n) ≥ A024939(n-2)` for `n ≥ 50`).

Conventions:
* The coefficient of `xⁿ` only involves the primes `p ≤ n`, so it is computed from the finite
  product over primes `p ≤ n`.
-/

namespace OMA.S_oeis_a046675

open Polynomial

/-- Coefficient of `xⁿ` in `∏_p (1 - x^p)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - X ^ p : ℤ[X])).coeff n

/-- `(-1)ⁿ a(n) ≥ 0` for `n ≥ 50`. -/
theorem main : ∀ n : ℕ, 50 ≤ n → 0 ≤ (-1 : ℤ) ^ n * a n := by
  sorry

end OMA.S_oeis_a046675
