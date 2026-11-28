import Mathlib

/-!
# Practical differences among consecutive primes

Zhi-Wei Sun's conjecture asks for infinitely many blocks of each length
`m + 1`, with `m > 0`, such that every positive difference of two primes
in the block is a practical number.

Source: https://oeis.org/A244349 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a244349

open scoped BigOperators

/-- The prime at the one-based index `n`. -/
noncomputable def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- Every positive integer up to a practical number is a sum of distinct
positive divisors of that number. -/
def IsPractical (d : ℕ) : Prop :=
  0 < d ∧ ∀ s : ℕ, 0 < s → s ≤ d →
    ∃ D : Finset ℕ, D ⊆ d.divisors ∧ (∑ a ∈ D, a) = s

theorem main : ∀ m : ℕ, 0 < m →
    Set.Infinite {n : ℕ | 0 < n ∧
      ∀ i j : ℕ, i < j → j ≤ m → IsPractical (primeAt (n + j) - primeAt (n + i))} := by
  sorry

end OMA.S_oeis_a244349
