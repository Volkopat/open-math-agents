import Mathlib

/-!
# Kimberling's conjecture on prime gaps containing twice a prime

Source: https://oeis.org/A059786 and https://oeis.org/A059788
Credit: @pyaf
-/

namespace OMA.S_oeis_a059786

/-- Double the n-th prime, with the OEIS index n starting at 1. -/
noncomputable def twicePrime (n : ℕ) : ℕ := 2 * Nat.nth Nat.Prime (n - 1)

/-- A059786, the least prime strictly above twice the n-th prime. -/
noncomputable def upper (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (twicePrime n + 1))

/-- A059788, the largest prime strictly below twice the n-th prime. -/
noncomputable def lower (n : ℕ) : ℕ :=
  ((Finset.range (twicePrime n)).filter Nat.Prime).sup id

theorem main : ∀ k : ℕ, 2 < k → Even k →
    Set.Infinite {n : ℕ | 0 < n ∧ upper n - lower n = k} := by
  sorry

end OMA.S_oeis_a059786
