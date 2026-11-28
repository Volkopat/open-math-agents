import Mathlib

/-!
# OEIS A080693: numbers of the form p²q + rs

Source: https://oeis.org/A080693
Numbers of the form `p² q + r s` with `p, q, r, s` (not necessarily distinct) primes.
A conjecture of Goldbach type says every number `≥ 26` is of this form.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a080693

theorem main :
    ∀ n : ℕ, 26 ≤ n → ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      n = p ^ 2 * q + r * s := by
  sorry

end OMA.S_oeis_a080693
