import Mathlib

/-!
# A088185: Numbers which are not the sum of two coprime semiprimes

Source: https://oeis.org/A088185
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A088185 lists the natural numbers which cannot be written as the sum of two
coprime semiprimes. Conjecture / question: This sequence is finite.
-/

namespace OMA.S_oeis_a088185

/-- A natural number is a semiprime if it is the product of two (not necessarily distinct) primes. -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

theorem main :
    Set.Finite {n : ℕ | ¬ ∃ a b : ℕ, IsSemiprime a ∧ IsSemiprime b ∧ Nat.Coprime a b ∧ a + b = n} := by
  sorry

end OMA.S_oeis_a088185
