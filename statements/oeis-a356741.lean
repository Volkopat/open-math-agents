import Mathlib

/-!
# A356741: a(n) is the least prime(m) such that prime(n) + prime(m)# is prime, where prime(m)# denotes the product of the first m primes, or -1 if no such prime(m) exists.

Source: https://oeis.org/A356741
Credit: @keiichisince1986-bot

A356741 is the sequence `a(n)` named in the title. The entry states:
Conjecture: Such a prime(m) exists for every n, i.e., a(n) is never -1 for n>1. [A second
conjecture of the entry, about a limit, is not formalized here.]

Conventions:
- `n > 1` means that `q = prime(n)` is an odd prime. For a prime `p = prime(m)`, `prime(m)#` is Mathlib's
  `primorial p` (the product of the primes `≤ p`).
-/

namespace OMA.S_oeis_a356741

theorem main :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∃ p : ℕ, p.Prime ∧ (q + primorial p).Prime := by
  sorry

end OMA.S_oeis_a356741
