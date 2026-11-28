import Mathlib

/-!
# Consecutive prime gaps centered between twin primes

Zhi-Wei Sun's conjecture asks for infinitely many runs of each positive
length in which each gap is the midpoint of a pair of twin primes.

Source: https://oeis.org/A244308 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a244308

/-- The gap following the prime at the one-based index `n`.
Mathlib indexes the primes from zero. -/
noncomputable def primeGapAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

theorem main : ∀ m : ℕ, 0 < m →
    Set.Infinite {n : ℕ | 0 < n ∧ ∀ i < m,
      let g := primeGapAt (n + i)
      0 < g ∧ (g - 1).Prime ∧ (g + 1).Prime} := by
  sorry

end OMA.S_oeis_a244308
