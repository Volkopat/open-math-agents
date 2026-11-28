import Mathlib

/-!
# A258429: Primes p such that p - 1 = (tau(p - 1) - 1)^k for some k >= 0, where tau(n) is the number of divisors of n (A000005).

Source: https://oeis.org/A258429
Credit: @luciusacarr

Data: 2, 5, 17, 65537 (corresponding k: 0, 2, 2, 4).

Conjecture (from the entry): the sequence is finite. `main` states it.

Reading of the source:
* `tau(m)` is the number of divisors of `m`, `(Nat.divisors m).card`.
* `k` ranges over the natural numbers `k ≥ 0` (k = 0 gives p = 2).
* With this reading the terms below 70000 are exactly the four listed (checked numerically).
-/

namespace OMA.S_oeis_a258429

/-- The terms of A258429. -/
def S : Set ℕ :=
  {p | p.Prime ∧ ∃ k : ℕ, p - 1 = ((Nat.divisors (p - 1)).card - 1) ^ k}

theorem main :
    -- The sequence is finite.
    S.Finite := by
  sorry

end OMA.S_oeis_a258429
