import Mathlib

/-!
# A102084: a(1) = 0; for n>0, write 2n=p+q (p, q prime), p*q maximal; then a(n)=p*q (see A073046).

Source: https://oeis.org/A102084
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

The definition of this sequence assumes the Goldbach conjecture: every even integer `2n >= 4`
can be written as the sum of two primes `p + q`.
-/

namespace OMA.S_oeis_a102084

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q := by
  sorry

end OMA.S_oeis_a102084
