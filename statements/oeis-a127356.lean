import Mathlib

/-!
# A127356: a(n) is the smallest k > 0 such that k^2 + prime(n) is prime.

Source: https://oeis.org/A127356
Credit: @keiichisince1986-bot

A127356 is the sequence `a(n)` named in the title. The entry states:
a(n) exists for all n on the Hardy-Littlewood conjecture F. - Charles R Greathouse IV, Jul 26 2012
(The entry attributes this to the Hardy-Littlewood conjecture F; the statement below is the
unconditional claim.)

Conventions:
- `prime(n)` ranges over all primes `p`; `a(n)` exists means that `k^2 + p` is prime for some `k > 0`.
-/

namespace OMA.S_oeis_a127356

theorem main :
    ∀ p : ℕ, p.Prime → ∃ k : ℕ, 0 < k ∧ (k ^ 2 + p).Prime := by
  sorry

end OMA.S_oeis_a127356
