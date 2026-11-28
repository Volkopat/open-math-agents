import Mathlib

/-!
# A276045: Primes p such that d(p*(2p+1)) = 8 where d(n) is the number of divisors of n (A000005).

Source: https://oeis.org/A276045
Credit: @luciusacarr

Data: 7, 13, 17, 19, 43, 47, 59, 61, 71, 79, 101, 107, 109, 149, 151, ...

From Anthony Hernandez, Aug 29 2016: Conjecture: this sequence is infinite. It appears that the
prime numbers in this sequence which have 7 for as final digit form the sequence A104164.
Conjecture: this sequence contains infinitely many twin primes. The first few twin primes in
this sequence are 17, 19, 59, 61, 107, 109, 521, 523, 599, 601, ...

`main` states the three claims, as a conjunction, in the order the source gives them.

Reading of the source:
* `d(m)` is the number of divisors of `m`, `(Nat.divisors m).card`.
* A104164 ("Sophie Germain type primes where 5*Prime[n] = 2*Prime[m] + 1") lists the primes `q`
  such that `2q + 1 = 5p` for a prime `p` (7, 17, 47, 107, ...).
* "Contains infinitely many twin primes": the listed examples are pairs `p, p + 2` with both
  members in the sequence (17 and 19, 59 and 61, ...), so it is read as: there are infinitely
  many `p` such that `p` and `p + 2` both belong to the sequence.
-/

namespace OMA.S_oeis_a276045

/-- The terms of A276045. -/
def S : Set ℕ := {p | p.Prime ∧ (Nat.divisors (p * (2 * p + 1))).card = 8}

theorem main :
    -- The sequence is infinite.
    S.Infinite ∧
    -- The terms ending in the digit 7 are exactly the terms of A104164.
    (∀ q : ℕ, (q ∈ S ∧ q % 10 = 7) ↔ (q.Prime ∧ ∃ p : ℕ, p.Prime ∧ 2 * q + 1 = 5 * p)) ∧
    -- The sequence contains infinitely many pairs of twin primes p, p + 2.
    {p : ℕ | p ∈ S ∧ p + 2 ∈ S}.Infinite := by
  sorry

end OMA.S_oeis_a276045
