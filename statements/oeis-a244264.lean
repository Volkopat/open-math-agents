import Mathlib

/-!
# Consecutive prime gaps that are powers of two

Zhi-Wei Sun's conjecture in OEIS A244264 asks for infinitely many runs of
each positive length in which every consecutive prime gap is a power of two.

Source: https://oeis.org/A244264 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a244264

/-- The gap following the prime at the one-based index `n`.
Mathlib's `Nat.nth` indexes the primes starting at zero. -/
noncomputable def primeGapAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

theorem main : ∀ m : ℕ, 0 < m →
    Set.Infinite {n : ℕ | 0 < n ∧ ∀ i < m, ∃ k : ℕ, primeGapAt (n + i) = 2 ^ k} := by
  sorry

end OMA.S_oeis_a244264
