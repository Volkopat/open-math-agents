import Mathlib

/-!
# A073703: Smallest prime p such that also p+prime(n)*2 is a prime.

Source: https://oeis.org/A073703
Credit: @keiichisince1986-bot

A073703 is the sequence `a(n)` named in the title. The entry states:
If Polignac's conjecture (1849) is correct, the sequence is defined for all n (as is A020483).
(The statement below is the claim that the sequence is defined for all n, unconditionally.)

Conventions:
- `prime(n)` ranges over all primes `q`; `a(n)` is defined when some prime `p` has `p + 2q` prime.
-/

namespace OMA.S_oeis_a073703

theorem main :
    ∀ q : ℕ, q.Prime → ∃ p : ℕ, p.Prime ∧ (p + 2 * q).Prime := by
  sorry

end OMA.S_oeis_a073703
