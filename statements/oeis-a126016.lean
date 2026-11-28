import Mathlib

/-!
# A126016: Numbers whose aliquot sequence does not terminate in 1.

Source: https://oeis.org/A126016
Credit: @luciusacarr

The entry (data 6, 25, 28, 95, 119, 143, 220) records the claim (Nathaniel J. Strout,
Nov 25 2018): for additional terms, if the Goldbach Conjecture is assumed, take any odd term,
subtract 1, and find two distinct primes that sum to it. Multiply the two primes and the product
is an element of the sequence. (The remark that for some numbers there is no such pair of
distinct primes, e.g. when the term minus 1 is a power of a prime, only concerns the existence
of the pair, not the claim.)

Reading of the source:
* The aliquot map is s(n) = sigma(n) - n, the sum of the proper divisors of n; the aliquot
  sequence of n is n, s(n), s(s(n)), ... . It terminates in 1 if some iterate equals 1.
  A term is a positive integer n with s^k(n) /= 1 for every k >= 0.
* Goldbach is only invoked to guarantee that a pair of primes exists; the claim itself is the
  implication: if n is an odd term and p, q are distinct primes with p + q = n - 1, then p*q is
  a term. It is stated here for every such pair (no Goldbach hypothesis is needed for it).
-/

namespace OMA.S_oeis_a126016

/-- The aliquot map `s(n) = σ(n) - n`, the sum of the proper divisors of `n`. -/
def s (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n

/-- `n` is a term: a positive integer whose aliquot sequence `n, s(n), s(s(n)), ...` never
reaches 1. -/
def InSeq (n : ℕ) : Prop := 0 < n ∧ ∀ k : ℕ, s^[k] n ≠ 1

theorem main : ∀ n, InSeq n → Odd n → ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    p + q = n - 1 → InSeq (p * q) := by
  sorry

end OMA.S_oeis_a126016
