import Mathlib

/-!
# OEIS A007921: numbers that are not the difference of two primes

Source: https://oeis.org/A007921 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

A007921 lists the positive integers that are not the difference of two primes:
7, 13, 19, 23, 25, 31, 33, 37, ... The entry states:

  Conjecturally, odd numbers k such that k+2 is composite.

For odd `k` the statement is elementary (a difference of two odd primes is even, so an odd
difference must be `p - 2`, i.e. `k + 2` prime). The conjectural content is the even case:
every positive even number is a difference of two primes (a weak form of de Polignac's
conjecture). For `k ≥ 1`, `k + 2 ≥ 3`, so `k + 2` composite is the same as `k + 2` not prime.

We formalize: for every `k ≥ 1`, `k` is not of the form `p - q` with `p, q` prime
(written additively as `p = q + k`) if and only if `k` is odd and `k + 2` is not prime.
-/

namespace OMA.S_oeis_a007921

/-- `k` is a difference of two primes: `p = q + k` for some primes `p` and `q`. -/
def IsPrimeDiff (k : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p = q + k

/-- Conjecture of A007921: the positive integers that are not differences of two primes are
exactly the odd `k` with `k + 2` composite. -/
theorem main : ∀ k : ℕ, 1 ≤ k → (¬ IsPrimeDiff k ↔ (Odd k ∧ ¬ (k + 2).Prime)) := by
  sorry

end OMA.S_oeis_a007921
