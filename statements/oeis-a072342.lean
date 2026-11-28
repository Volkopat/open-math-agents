import Mathlib

/-!
# A072342: Least natural number k such that k*reverse(n) + 1 is prime

Source: https://oeis.org/A072342
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = the least natural number k such that k*reverse(n) + 1 is prime.
Conjecture: a(n) is less than or equal to n for all n >= 1.
-/

namespace OMA.S_oeis_a072342

/-- Decimal digit reversal of `n`. -/
def reverseDigits (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, k ≤ n ∧ Nat.Prime (k * reverseDigits n + 1) := by
  sorry

end OMA.S_oeis_a072342
