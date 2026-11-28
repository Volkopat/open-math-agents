import Mathlib

/-!
# Consecutive triangular prime gaps

Zhi-Wei Sun's conjecture in OEIS A244254 asks for infinitely many runs of
each positive length in which every consecutive prime gap is triangular.

Source: https://oeis.org/A244254 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a244254

/-- The gap following the prime at the one-based index `n`.
Mathlib's `Nat.nth` indexes the primes starting at zero. -/
noncomputable def primeGapAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

theorem main : ∀ m : ℕ, 0 < m →
    Set.Infinite {n : ℕ | 0 < n ∧
      ∀ i < m, ∃ k : ℕ, primeGapAt (n + i) = k * (k + 1) / 2} := by
  sorry

end OMA.S_oeis_a244254
