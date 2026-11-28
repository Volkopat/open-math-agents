import Mathlib

/-!
# OEIS A073316: a common shift making two even numbers prime

Source: https://oeis.org/A073316
`a n = max_{1 ≤ j < n} d(j)`, where `d(j)` is the smallest positive number such that `2j + d(j)`
and `2n + d(j)` are both prime. Conjecture: `a(n) < 2n`; equivalently, for any positive even
numbers `e₁ < e₂ ≤ 2n` there is a positive `d < 2n` with `e₁ + d` and `e₂ + d` prime (a
conjecture of Erdős mentioned by Guy, end of C1).

Conventions. `n ≥ 2`; the conjecture is stated directly: for every `1 ≤ j < n` some
`0 < d < 2n` makes `2j + d` and `2n + d` prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a073316

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∀ j : ℕ, 1 ≤ j → j < n →
      ∃ d : ℕ, 0 < d ∧ d < 2 * n ∧ (2 * j + d).Prime ∧ (2 * n + d).Prime := by
  sorry

end OMA.S_oeis_a073316
