import Mathlib

/-!
# Carry-free arithmetic derivatives in primorial base

For a product of distinct primes the arithmetic derivative is the sum of the
quotients by those primes. The place value at index j is the product of the
first j primes, and the digit at that place has radix the next prime.

Source: https://oeis.org/A380476.
-/
namespace OMA.S_oeis_a380476

noncomputable def place (j : ℕ) : ℕ := ∏ i ∈ Finset.range j, Nat.nth Nat.Prime i

noncomputable def digit (n j : ℕ) : ℕ := (n / place j) % Nat.nth Nat.Prime j

def noCarries (n : ℕ) (s : Finset ℕ) : Prop :=
  ∀ j : ℕ, (∑ p ∈ s, digit (n/p) j) < Nat.nth Nat.Prime j

/-- A380476 consists of the squarefree carry-free terms with at least four factors. -/
theorem main : ∀ n : ℕ, Squarefree n → 4 ≤ n.primeFactors.card →
    noCarries n n.primeFactors → n.primeFactors.card = 4 := by
  sorry

end OMA.S_oeis_a380476
