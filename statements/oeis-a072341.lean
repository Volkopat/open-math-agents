import Mathlib

/-!
# A072341: Least natural number k such that k*sigma(n) + 1 is prime

Source: https://oeis.org/A072341
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = the least natural number k such that k*sigma(n) + 1 is prime.
Conjecture: a(n) is less than or equal to n for all n >= 1.
-/

namespace OMA.S_oeis_a072341

/-- Sum of positive divisors of `n`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, k ≤ n ∧ Nat.Prime (k * sigma n + 1) := by
  sorry

end OMA.S_oeis_a072341
