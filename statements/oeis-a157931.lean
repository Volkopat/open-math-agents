import Mathlib

/-!
# A157931: Numbers that are both the sum and the product of two primes.

Source: https://oeis.org/A157931
Credit: @agchua

Comment of A157931 (N. J. A. Sloane, Mar 14 2009):
  Assuming the Goldbach conjecture, this is A001358 intersect (A005843 union A052147), since an
  odd number n is the sum of two primes iff n-2 is prime.
A001358 is the semiprimes (products of two primes, not necessarily distinct), A005843 the even
numbers, A052147 the numbers p + 2 with p prime. The Goldbach conjecture is stated as: every even
n > 2 is the sum of two primes. Both parts of the comment are stated: the unconditional claim about
odd numbers (for odd n, n - 2 is the natural-number difference; n = 1 is covered, as neither side
holds) and the description of the sequence under the Goldbach conjecture.
-/

namespace OMA.S_oeis_a157931

/-- n is the sum of two primes. -/
def IsSumTwoPrimes (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- n is the product of two primes (a semiprime, A001358). -/
def IsProdTwoPrimes (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p * q = n

/-- Membership in A157931: n is both the sum and the product of two primes. -/
def InSeq (n : ℕ) : Prop := IsSumTwoPrimes n ∧ IsProdTwoPrimes n

/-- The Goldbach conjecture: every even number greater than 2 is the sum of two primes. -/
def Goldbach : Prop := ∀ n : ℕ, 2 < n → Even n → IsSumTwoPrimes n

/-- The comment: an odd n is the sum of two primes iff n - 2 is prime; and, assuming the
Goldbach conjecture, n is in A157931 iff n is a semiprime that is even or a prime plus 2. -/
theorem main : (∀ n : ℕ, Odd n → (IsSumTwoPrimes n ↔ (n - 2).Prime)) ∧
    (Goldbach → ∀ n : ℕ, (InSeq n ↔ (IsProdTwoPrimes n ∧
      (Even n ∨ ∃ p : ℕ, p.Prime ∧ n = p + 2)))) := by
  sorry

end OMA.S_oeis_a157931
