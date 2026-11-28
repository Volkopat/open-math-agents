import Mathlib

/-!
A075082: Numbers n such that n! is a product of distinct factorials k!*l!*m!*... with k, l, m, etc. < n.

Source: https://oeis.org/A075082
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Subsequence of A034878 (all n such that n! is a product of smaller factorials). It is conjectured that A034878 and A001013 (Jordan-Polya numbers = products of factorials) are the same sequence (except for the numbers 2, 9 and 10).
-/

namespace OMA.S_oeis_a075082

/-- `n` belongs to A034878: `n!` is a product of factorials of integers in `[2, n)`. -/
def InA034878 (n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ k ∈ s, 2 ≤ k ∧ k < n) ∧ n.factorial = (s.map Nat.factorial).prod

/-- `n` is a Jordan-Polya number (A001013): `n` is a product of factorials. -/
def IsJordanPolya (n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ k ∈ s, 2 ≤ k) ∧ n = (s.map Nat.factorial).prod

/-- Conjecture: A034878 and A001013 agree for all positive integers except 2, 9, and 10. -/
theorem main :
    ∀ n : ℕ, 0 < n → n ≠ 2 → n ≠ 9 → n ≠ 10 →
      (InA034878 n ↔ IsJordanPolya n) := by sorry

end OMA.S_oeis_a075082
