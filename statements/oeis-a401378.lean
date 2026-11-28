import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

/-!
# A401378: Prime factors of the coprime part of a divisor sum

Source: https://oeis.org/A401378 (Antti Karttunen)
Credit: @Alienchisel

For a square with at least two distinct prime factors forming a consecutive
block of primes, the largest divisor of its divisor sum coprime to the
original square has at least two distinct prime factors. The latter count
is the value of OEIS A401379 at the square.
-/

namespace OMA.S_oeis_a401378

/-- No prime between two prime factors of this number is missing from its prime factors. -/
def HasConsecutivePrimeFactors (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ∀ r : ℕ,
    r.Prime → p < r → r < q → r ∈ n.primeFactors

/-- The largest divisor of the sum of the positive divisors of n that is coprime to n. -/
def CoprimePartOfDivisorSum (n : ℕ) : ℕ :=
  let divisorSum := n.divisors.sum id
  (divisorSum.divisors.filter fun d => d.Coprime n).sup id

theorem main : ∀ n : ℕ, IsSquare n → 2 ≤ n.primeFactors.card →
    HasConsecutivePrimeFactors n → 2 ≤ (CoprimePartOfDivisorSum n).primeFactors.card := by
  sorry

end OMA.S_oeis_a401378
