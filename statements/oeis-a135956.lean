import Mathlib

/-!
# A135956: Members of A050937 (nonprime Fibonacci numbers with prime index) with 5 or more distinct prime factors.

Source: https://oeis.org/A135956
Credit: @agchua

Comment of A135956 (unsigned; the entry is by Artur Jasinski, Dec 08 2007):
  Conjecture: all numbers in this sequence are product of 5 or more sum of two squares
Offset 1. The terms are the numbers n = F(p) (Fibonacci numbers, F(1) = F(2) = 1) with p prime,
n not prime, and at least five distinct prime factors, as in the name and in the entry's
program (Mathematica: Length[FactorInteger[Fibonacci[Prime[n]]]] > 4).
Reading of the conjecture: the factors are the prime factors of the term, so the claim is that
every prime factor of a term is a sum of two squares of natural numbers. (With arbitrary factors
the claim would say nothing: 1 = 1^2 + 0^2, and F(2m+1) = F(m+1)^2 + F(m)^2 is itself a sum of
two squares.)
-/

namespace OMA.S_oeis_a135956

/-- n is a term of A135956: n = F(p) for a prime p, n is not prime, and n has at least five
distinct prime factors. -/
def InSeq (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n = Nat.fib p ∧ ¬ n.Prime ∧ 5 ≤ n.primeFactors.card

/-- The conjecture: every prime factor of a term of A135956 is a sum of two squares. -/
theorem main : ∀ n : ℕ, InSeq n → ∀ q ∈ n.primeFactors, ∃ x y : ℕ, q = x ^ 2 + y ^ 2 := by
  sorry

end OMA.S_oeis_a135956
