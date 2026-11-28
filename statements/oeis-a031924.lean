import Mathlib

/-!
# A031924: Primes followed by a gap of 6

Source: https://oeis.org/A031924
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (OEIS entry, 2014):
Let a(n) (1-indexed) be the n-th prime p whose next prime is p + 6.
Then the sequence is infinite, and for every n >= 7746,
  a(n + 1) < a(n)^(1 + 1/n),
i.e., a(n)^(1/n) is strictly decreasing for n >= 7746.
-/

namespace OMA.S_oeis_a031924

/-- Predicate that p is a prime whose next prime is p + 6. -/
def isGap6Prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 6) ∧ ∀ q : ℕ, p < q → q < p + 6 → ¬ Nat.Prime q

/-- The n-th prime followed by a gap of 6 (1-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isGap6Prime (n - 1)

/-- Conjecture: isGap6Prime is infinite and a(n+1) < a(n)^(1 + 1/n) for all n >= 7746. -/
theorem main :
    {p : ℕ | isGap6Prime p}.Infinite ∧
    ∀ n : ℕ, 7746 ≤ n → (a (n + 1) : ℝ) < (a n : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a031924
