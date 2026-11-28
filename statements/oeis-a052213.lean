import Mathlib

/-!
# A052213: prime signatures and products of divisor counts

The prime signature is the multiset of positive exponents in a prime
factorization. The conjecture says that two consecutive positive integers
have the same prime signature exactly when the products of their divisors'
divisor counts agree.

Source: https://oeis.org/A052213
-/

namespace OMA.S_oeis_a052213

open Finset

def primeSignature (n : ℕ) : Multiset ℕ :=
  n.primeFactors.val.map n.factorization

def divisorProduct (n : ℕ) : ℕ :=
  ∏ d ∈ n.divisors, d.divisors.card

theorem main : ∀ n : ℕ, 0 < n →
    (primeSignature n = primeSignature (n + 1) ↔
      divisorProduct n = divisorProduct (n + 1)) := by
  sorry

end OMA.S_oeis_a052213
