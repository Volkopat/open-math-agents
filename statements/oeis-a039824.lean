import Mathlib

/-!
# OEIS A039824: distinct coefficient values

Source: https://oeis.org/A039824
`a n` is the number of different coefficient values in the expansion of
`∏_{i=1}^{n} (1 + q + q³ + ⋯ + q^(2i-1))` (1, 2, 4, 11, 20, …). Conjecture: for `n > 6`,
`a(n) = n² - 3`.

Conventions. The `i`-th factor is `1 + ∑_{j<i} q^(2j+1)`. "Coefficient values" are the
coefficients of `q^0, …, q^deg` (for `n = 1` this gives `{1}`, matching `a 1 = 1`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a039824

open Polynomial

/-- The product `∏_{i=1}^{n} (1 + q + q³ + ⋯ + q^(2i-1))`. -/
noncomputable def P (n : ℕ) : ℕ[X] :=
  ∏ i ∈ Finset.Icc 1 n, (1 + ∑ j ∈ Finset.range i, X ^ (2 * j + 1))

/-- Number of distinct coefficient values of `P n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range ((P n).natDegree + 1)).image fun k => (P n).coeff k).card

theorem main : ∀ n : ℕ, 6 < n → a n = n ^ 2 - 3 := by
  sorry

end OMA.S_oeis_a039824
