import Mathlib

/-!
# Melfi's conjecture on quintuples of practical numbers

Source: https://oeis.org/A287683
Credit: @petrovortex

Giuseppe Melfi, *On 5-Tuples of Twin Practical Numbers* (1999), Conjecture 4, p. 725.
-/

namespace OMA.S_oeis_a287683

open scoped BigOperators

/-- For a practical number `m`, each positive integer up to `m` is a sum of distinct divisors of `m`. -/
def IsPractical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, 0 < k → k ≤ m →
    ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- Infinitely many centers give practical numbers at all five offsets. -/
theorem main :
    {n : ℕ | 6 < n ∧ IsPractical (n - 6) ∧ IsPractical (n - 2) ∧ IsPractical n ∧
      IsPractical (n + 2) ∧ IsPractical (n + 6)}.Infinite := by
  sorry

end OMA.S_oeis_a287683
