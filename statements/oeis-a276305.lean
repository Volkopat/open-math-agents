import Mathlib

/-!
# A276305: Primes p such that d(p*(2p+1)) = 12 where d(n) is the number of divisors of n (A000005).

Source: https://oeis.org/A276305
Credit: @luciusacarr

Data: 31, 37, 73, 103, 137, 139, 181, 193, 211, 269, ...

Conjecture (from the entry): this sequence is infinite. `main` states it.

Reading of the source:
* `d(m)` is the number of divisors of `m`, `(Nat.divisors m).card`.
-/

namespace OMA.S_oeis_a276305

/-- The terms of A276305. -/
def S : Set ℕ := {p | p.Prime ∧ (Nat.divisors (p * (2 * p + 1))).card = 12}

theorem main :
    -- The sequence is infinite.
    S.Infinite := by
  sorry

end OMA.S_oeis_a276305
