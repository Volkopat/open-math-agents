import Mathlib

/-!
# A276307: Primes p such that d(p*(2p+1)) = 16 where d(n) is the number of divisors of n (A000005).

Source: https://oeis.org/A276307
Credit: @luciusacarr

Data: 67, 97, 127, 199, 227, 229, 241, 277, 307, 313, ...

Conjecture (from the entry): this sequence is infinite. `main` states it.

Reading of the source:
* `d(m)` is the number of divisors of `m`, `(Nat.divisors m).card`.
-/

namespace OMA.S_oeis_a276307

/-- The terms of A276307. -/
def S : Set ℕ := {p | p.Prime ∧ (Nat.divisors (p * (2 * p + 1))).card = 16}

theorem main :
    -- The sequence is infinite.
    S.Infinite := by
  sorry

end OMA.S_oeis_a276307
