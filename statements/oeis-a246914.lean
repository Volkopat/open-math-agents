import Mathlib

/-!
# A246914: Primes p such that sigma(2p+1) = 3*(p+1).

Source: https://oeis.org/A246914
Credit: @azmiozgen

Conjecture (Jaroslav Krizek, Sep 28 2014): the terms are also the primes p such that
sigma(2p+1) mod p = 3.

Formalization notes:
* Stated for every prime p: sigma(2p+1) = 3(p+1) if and only if sigma(2p+1) mod p = 3.
* Controls (computed): the primes below 200000 with sigma(2p+1) = 3(p+1) are 7, 103, 1487,
  9679, 73727, as in the entry, and the two conditions agree for every prime below 200000.
-/

namespace OMA.S_oeis_a246914

open ArithmeticFunction

/-- Krizek's conjecture: for primes `p`, `σ(2p+1) = 3(p+1)` iff `σ(2p+1) mod p = 3`. -/
theorem main :
    ∀ p : ℕ, p.Prime → (sigma 1 (2 * p + 1) = 3 * (p + 1) ↔ sigma 1 (2 * p + 1) % p = 3) := by
  sorry

end OMA.S_oeis_a246914
