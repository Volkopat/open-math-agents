import Mathlib

/-!
# A358318: For n >= 5, a(n) is the number of zeros that need to be inserted to the left of the ones digit of the n-th prime so that the result is composite.

Source: https://oeis.org/A358318
Credit: @darealpandaboi

Conjecture: the sequence is bounded.

Translation notes.
* Inserting k zeros to the left of the ones digit of p = 10*m + d gives m * 10^(k+1) + d.
  a(n) is the least k >= 1 making this composite, for p the n-th prime, n >= 5 (p >= 11).
  The result is at least 10^(k+1) > 1, so composite means not prime.
* a is bounded exactly when some B works for every such prime: for each prime p >= 11 some
  k with 1 <= k <= B makes the result composite (then a(n) <= B). This also asserts that a(n)
  is defined.
* This reproduces the listed data (checked by computer); for primes 11 <= p < 200000 the
  largest value is 7.
-/

namespace OMA.S_oeis_a358318

theorem main : ∃ B : ℕ, ∀ p : ℕ, p.Prime → 11 ≤ p →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ B ∧ ¬ (p / 10 * 10 ^ (k + 1) + p % 10).Prime := by
  sorry

end OMA.S_oeis_a358318
