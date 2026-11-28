import Mathlib

/-!
# A100351: Numbers n such that n-2^k is a semiprime for all k > 0 with 2^k < n.

Source: https://oeis.org/A100351
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: this sequence is finite.
-/

namespace OMA.S_oeis_a100351

/-- A natural number is semiprime if it is the product of two (not necessarily distinct) primes. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ m = q * r

theorem main :
    {n : ℕ | ∀ k : ℕ, 0 < k → 2 ^ k < n → IsSemiprime (n - 2 ^ k)}.Finite := by
  sorry

end OMA.S_oeis_a100351
