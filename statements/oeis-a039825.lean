import Mathlib

/-!
# OEIS A039825: exponents of a `q`-series

Source: https://oeis.org/A039825
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ⌊(n² + n + 8)/4⌋` (`n ≥ 0`): `2, 2, 3, 5, 7, 9, 12, 16, 20, …`. Conjecture (OEIS entry):
apart from the first term, the terms are the exponents in the expansion of
`∑_{n ≥ 1} q^(3n) ∏_{k ≥ 2n} (1 - q^k) = q³ - q⁵ - q⁷ + q⁹ + q¹² - q¹⁶ - q²⁰ + ⋯`.

Conventions:
* "The exponents in the expansion" are the `m` with nonzero coefficient. The coefficient of `q^m`
  only involves the summands with `3n ≤ m` and the factors with `k ≤ m`, so it is computed from
  finite products. "Apart from the first term" (`a(0) = 2`; `a(1) = 2` as well) means the set of
  exponents is `{a(n) | n ≥ 2}`.
-/

namespace OMA.S_oeis_a039825

open Polynomial

/-- `a(n) = ⌊(n² + n + 8)/4⌋`. -/
def a (n : ℕ) : ℕ := (n ^ 2 + n + 8) / 4

/-- Coefficient of `q^m` in `∑_{n ≥ 1} q^(3n) ∏_{k ≥ 2n} (1 - q^k)`. -/
noncomputable def coeffAt (m : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 m,
    (X ^ (3 * n) * ∏ k ∈ Finset.Icc (2 * n) m, (1 - X ^ k : ℤ[X])).coeff m

/-- The exponents with nonzero coefficient are exactly `a(n)`, `n ≥ 2`. -/
theorem main : ∀ m : ℕ, coeffAt m ≠ 0 ↔ ∃ n : ℕ, 2 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a039825
