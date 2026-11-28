import Mathlib

/-!
# A065406: Mersenne prime exponents that are Sophie Germain primes

Source: https://oeis.org/A065406
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A065/A065406.seq
Credit: @Bondyboy2001

The sequence consists of primes `p` such that `2^p - 1` is prime (so `p` is a Mersenne prime
exponent) and `2p + 1` is also prime (so `p` is a Sophie Germain prime). Boklan and Conway
conjectured that this sequence is finite.
-/

namespace OMA.S_oeis_a065406

/-- Membership in A065406. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ (2 ^ p - 1).Prime ∧ (2 * p + 1).Prime

theorem main : {p : ℕ | IsTerm p}.Finite := by
  sorry

end OMA.S_oeis_a065406
