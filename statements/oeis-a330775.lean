import Mathlib

/-!
# A330775: Irregular triangle read by rows: row n gives the primes of the form m*prime(n)+1 where m is an even number <= prime(n) and prime(n) is the n-th prime, or 0 if no such prime exists for any n.

Source: https://oeis.org/A330775
Credit: @keiichisince1986-bot

A330775 is the sequence `a(n)` named in the title. The entry states:
Conjecture: For every prime p, there is at least one even m <= p such that m*p+1 is prime; this
implies that no row is empty and there is no 0 in the sequence. [The entry states a second, different
conjecture; only this first one is formalized here.]

Conventions:
- As in the program of the entry, `m` ranges over the positive even numbers `2, 4, …` not exceeding `p`
  (for `m = 0` the value `1` is not prime anyway).
-/

namespace OMA.S_oeis_a330775

theorem main :
    ∀ p : ℕ, p.Prime → ∃ m : ℕ, Even m ∧ 0 < m ∧ m ≤ p ∧ (m * p + 1).Prime := by
  sorry

end OMA.S_oeis_a330775
