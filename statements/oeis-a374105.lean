import Mathlib

/-!
# Prime exponents in OEIS A374105

Aurelien Gibier conjectured that every exponent in A374105 is prime.
Writing the quotient as a prime number `p` and clearing its denominator
expresses both exact divisibility by 13 and primality of the quotient.

Source: https://oeis.org/A374105
Credit: @DrSubspace
-/

namespace OMA.S_oeis_a374105

theorem main : ∀ k p : ℕ, p.Prime → 9 ^ k + 3 ^ k + 1 = 13 * p → k.Prime := by
  sorry

end OMA.S_oeis_a374105
