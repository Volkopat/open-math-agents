import Mathlib

/-!
# OEIS A001653: solutions of the Markoff-type equation for m = 2

Source: https://oeis.org/A001653
`a 0 = 1`, `a 1 = 5`, `a (n+2) = 6 a (n+1) - a n` (A001653: 1, 5, 29, 169, …). From the entry
(Wolfdieter Lang, 2018): the consecutive pairs `(a n, a (n+1))` give all proper positive
solutions `m₁ < m₂` of `m₁² - 6 m₁ m₂ + m₂² = -4`, the Markoff-type equation for `m = 2`.
`main` states this characterisation.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a001653

/-- A001653. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 5
  | n + 2 => 6 * a (n + 1) - a n

theorem main :
    ∀ m₁ m₂ : ℤ, 0 < m₁ → m₁ < m₂ →
      (m₁ ^ 2 - 6 * m₁ * m₂ + m₂ ^ 2 = -4 ↔ ∃ n : ℕ, m₁ = a n ∧ m₂ = a (n + 1)) := by
  sorry

end OMA.S_oeis_a001653
