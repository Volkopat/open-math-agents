import Mathlib

/-!
# A070251: Conjectures on unrelated-factorial numbers

Source: https://oeis.org/A070251
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A070251: Unrelated-factorial numbers: product of numbers unrelated to n (numbers
in 1..n which have a common divisor > 1 with n but do not divide n).

Statement:
Conjectures:
1. a(6) = 4 is the only powerful term that exceeds 1.
2. a(8) = a(9) = 6 is the only squarefree number exceeding 1 that appears in the sequence.
3. For composite n > 9 not an even squarefree semiprime (i.e., not 2*p for an odd prime p),
   n divides a(n).
-/

namespace OMA.S_oeis_a070251

/-- `A070251(n)`: product of all `1 <= k <= n` with `gcd(k, n) > 1` and `¬ (k ∣ n)`. -/
def a (n : ℕ) : ℕ :=
  ∏ k ∈ (Finset.Icc 1 n).filter (fun k => 1 < Nat.gcd k n ∧ ¬ k ∣ n), k

/-- A positive integer `m` is powerful if `p^2 ∣ m` for every prime `p ∣ m`. -/
def IsPowerful (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m

theorem main :
    (∀ n : ℕ, 1 < a n → IsPowerful (a n) → a n = 4) ∧
    (∀ n : ℕ, 1 < a n → Squarefree (a n) → a n = 6) ∧
    (∀ n : ℕ, 9 < n → ¬ Nat.Prime n → (¬ ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ n = 2 * p) →
      n ∣ a n) := by
  sorry

end OMA.S_oeis_a070251
