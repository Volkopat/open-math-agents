import Mathlib

/-!
# A158361: Primes p with property that Q = p^4 + 2^4 is prime.

Source: https://oeis.org/A158361
Credit: @sntntHb

Conjecture (stated on the OEIS page): the sequence is infinite, i.e. there are infinitely many
primes `p` such that `p^4 + 2^4` is also prime.
-/

namespace OMA.S_oeis_a158361

theorem main : {p : ℕ | p.Prime ∧ (p ^ 4 + 2 ^ 4).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a158361
