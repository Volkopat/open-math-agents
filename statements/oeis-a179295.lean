import Mathlib

/-!
# A179295: a(n) is the least prime number such that prime(n)+a(n)+1 is a prime or -1 if no such prime number exists.

Source: https://oeis.org/A179295
Credit: @keiichisince1986-bot

A179295 is the sequence `a(n)` named in the title. The entry states:
If Maillet's conjecture is true, then a(n) != -1 for all n. - Chai Wah Wu, Aug 01 2017 (The statement
below is the claim that a(n) exists for all n, unconditionally.)

Conventions:
- `prime(n)` ranges over all primes `p`; `a(n)` exists means that `p + q + 1` is prime for some prime `q`.
-/

namespace OMA.S_oeis_a179295

theorem main :
    ∀ p : ℕ, p.Prime → ∃ q : ℕ, q.Prime ∧ (p + q + 1).Prime := by
  sorry

end OMA.S_oeis_a179295
