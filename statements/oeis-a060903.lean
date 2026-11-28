import Mathlib

/-!
# OEIS A060903: a bound for the sum of divisors

Source: https://oeis.org/A060903
`a n = ⌊6 n √n / π²⌋`. Conjecture (Wilson v, 2014): the sum of the divisors of `n` is less than
`a(n)` for `n > 12`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a060903

open Real

theorem main :
    ∀ n : ℕ, 12 < n → ∑ d ∈ n.divisors, d < ⌊6 * n * √n / π ^ 2⌋₊ := by
  sorry

end OMA.S_oeis_a060903
