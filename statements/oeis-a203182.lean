import Mathlib

/-!
# OEIS A203182

The sequence consists of primes whose two neighbours have equal sums of distinct
prime divisors. Its infinitude is conjectured by Michel Lagneau.

Source: https://oeis.org/A203182
Credit: @AlfredMelson
-/

namespace OMA.S_oeis_a203182

/-- A008472 counts each prime divisor once in the sum. -/
def primeDivisorSum (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

theorem main :
    {p : ℕ | p.Prime ∧ primeDivisorSum (p - 1) = primeDivisorSum (p + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a203182
