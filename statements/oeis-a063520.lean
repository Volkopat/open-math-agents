import Mathlib

/-!
# OEIS A063520: when the sum divides the product

Source: https://oeis.org/A063520
`a n` is the number of solutions `(r, s, t)`, `r ≥ s ≥ t > 0`, of `r s t = n (r + s + t)`.
Conjecture (David W. Wilson): the positive integers `n` with `a(n) > 0` are all positive
integers except `2, 4, 7` and `11`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a063520

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((∃ r s t : ℕ, 0 < t ∧ t ≤ s ∧ s ≤ r ∧ r * s * t = n * (r + s + t)) ↔
        n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 7 ∧ n ≠ 11) := by
  sorry

end OMA.S_oeis_a063520
