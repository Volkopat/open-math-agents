import Mathlib

/-!
# A069869: Existence of a prime formed by concatenating parts of a partition of n

Source: https://oeis.org/A069869
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A069869: Largest prime that is a concatenation of the parts of a partition of n,
or 0 if no such prime exists.

Statement:
Conjecture: a(n) = 0 only for n = 1 or n = 3*k with k > 1.

Conventions:
- A composition (ordered partition) of `n` is a list `L : List ℕ` of positive integers
  summing to `n`.
- Decimal concatenation of `L` writes the base-10 digits of each part in order (most
  significant digit first).
-/

namespace OMA.S_oeis_a069869

/-- Decimal concatenation of a list of positive natural numbers. -/
def concat10 (L : List ℕ) : ℕ :=
  Nat.ofDigits 10 ((L.flatMap (fun m => (Nat.digits 10 m).reverse)).reverse)

/-- There exists a prime obtained by concatenating the parts of some partition of `n`. -/
def HasPartitionPrime (n : ℕ) : Prop :=
  ∃ L : List ℕ, (∀ x ∈ L, 0 < x) ∧ L.sum = n ∧ Nat.Prime (concat10 L)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (¬ HasPartitionPrime n ↔ n = 1 ∨ ∃ k : ℕ, 1 < k ∧ n = 3 * k) := by
  sorry

end OMA.S_oeis_a069869
