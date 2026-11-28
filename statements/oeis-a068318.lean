import Mathlib

/-!
# A068318: Sum of prime factors of n-th semiprime.

Source: https://oeis.org/A068318
Credit: @agchua

Comment of A068318 (Jianing Song, May 26 2021; the entry is by Reinhard Zumkeller, Feb 27 2002):
  Odd k is a term if and only if k - 2 is prime. Goldbach's conjecture implies that every even
  number k >= 4 is a term.
The sequence has offset 1: a(n) is the sum of the prime factors, counted with multiplicity, of
the n-th semiprime A001358(n) (4, 6, 9, 10, 14, ...), that is, of the n-th number with exactly two
prime factors counted with multiplicity. Nat.nth counts from 0, so a(n) uses the index n - 1.
A number k is a term when k = a(n) for some n >= 1. Goldbach's conjecture is stated in its usual
form: every even number greater than 2 is the sum of two primes. Both claims are stated.
-/

namespace OMA.S_oeis_a068318

/-- A068318(n): the sum of the prime factors (with multiplicity) of the n-th semiprime. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.nth (fun s : ℕ => s.primeFactorsList.length = 2) (n - 1)).primeFactorsList.sum

/-- Goldbach's conjecture: every even number greater than 2 is the sum of two primes. -/
def Goldbach : Prop := ∀ m : ℕ, 2 < m → Even m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m

/-- The comment: an odd k is a term iff k - 2 is prime, and Goldbach's conjecture implies that
every even k >= 4 is a term. -/
theorem main :
    (∀ k : ℕ, Odd k → ((∃ n : ℕ, 1 ≤ n ∧ a n = k) ↔ (k - 2).Prime)) ∧
    (Goldbach → ∀ k : ℕ, 4 ≤ k → Even k → ∃ n : ℕ, 1 ≤ n ∧ a n = k) := by
  sorry

end OMA.S_oeis_a068318
