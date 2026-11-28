import Mathlib

/-!
# A135954: Nonprime Fibonacci numbers with prime indices (A050937) that have exactly 3 prime factors.

Source: https://oeis.org/A135954
Credit: @agchua

Comment of A135954 (unsigned; the entry is by Artur Jasinski, Dec 08 2007):
  Conjecture: All numbers in this sequence are products of three sums of two squares.
Offset 1. The terms are the numbers n = F(p) (Fibonacci numbers, F(1) = F(2) = 1) with p prime,
n not prime, and exactly three distinct prime factors, as in the entry's programs
(Mathematica: Length[FactorInteger[Fibonacci[Prime[n]]]] == 3; PARI: omega(p) == 3).
Reading of the conjecture: the three factors are the prime factors of the term, so the claim is
that every prime factor of a term is a sum of two squares of natural numbers. (With arbitrary
factors the claim would say nothing: 1 = 1^2 + 0^2, and F(2m+1) = F(m+1)^2 + F(m)^2 is itself
a sum of two squares.)
-/

namespace OMA.S_oeis_a135954

/-- n is a term of A135954: n = F(p) for a prime p, n is not prime, and n has exactly three
distinct prime factors. -/
def InSeq (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n = Nat.fib p ∧ ¬ n.Prime ∧ n.primeFactors.card = 3

/-- The conjecture: every prime factor of a term of A135954 is a sum of two squares. -/
theorem main : ∀ n : ℕ, InSeq n → ∀ q ∈ n.primeFactors, ∃ x y : ℕ, q = x ^ 2 + y ^ 2 := by
  sorry

end OMA.S_oeis_a135954
