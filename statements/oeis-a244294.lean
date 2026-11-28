import Mathlib

/-!
# Consecutive prime gaps with prime halves

Zhi-Wei Sun's conjecture asks for infinitely many runs of each positive
length in which every consecutive prime gap is twice a prime.

Source: https://oeis.org/A244294 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a244294

/-- The gap following the prime at the one-based index `n`.
Mathlib indexes the primes from zero. -/
noncomputable def primeGapAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

theorem main : ∀ m : ℕ, 0 < m →
    Set.Infinite {n : ℕ | 0 < n ∧
      ∀ i < m, ∃ p : ℕ, p.Prime ∧ primeGapAt (n + i) = 2 * p} := by
  sorry

end OMA.S_oeis_a244294
