import Mathlib

/-!
# A080435: Greedy sequence with unique prime pairwise sums

Source: https://oeis.org/A080435
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(1) = 1; a(n) = least k > a(n-1) such that each prime of form a(i)+a(j) occurs for unique i <= j.
Conjecture: There are infinitely many primes not of the form a(i)+a(j).
-/

namespace OMA.S_oeis_a080435

def IsValidPrefix (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i₁ j₁ i₂ j₂ : ℕ,
    1 ≤ i₁ → i₁ ≤ j₁ → j₁ ≤ n →
    1 ≤ i₂ → i₂ ≤ j₂ → j₂ ≤ n →
    Nat.Prime (a i₁ + a j₁) →
    a i₁ + a j₁ = a i₂ + a j₂ →
    i₁ = i₂ ∧ j₁ = j₂

def IsA080435 (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
  ∀ n : ℕ, 2 ≤ n →
    a (n - 1) < a n ∧
    IsValidPrefix a n ∧
    ∀ k : ℕ, a (n - 1) < k → k < a n → ¬ IsValidPrefix (Function.update a n k) n

theorem main :
    ∀ a : ℕ → ℕ, IsA080435 a →
      Set.Infinite {p : ℕ | Nat.Prime p ∧ ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i + a j ≠ p} := by
  sorry

end OMA.S_oeis_a080435
