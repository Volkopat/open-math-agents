import Mathlib

/-!
# OEIS A007540: a power-sum characterization of the Wilson primes

Source: https://oeis.org/A007540
Credit: @sntntHb

A007540: Wilson primes, primes `p` such that `(p-1)! == -1 (mod p^2)` (5, 13, 563, ...).

Conjecture (Thomas Ordowski and Giovanni Resta, Jul 25 2018): the Wilson primes are the odd
primes `p` such that `1^(p-1) + 2^(p-1) + ... + (p-1)^(p-1) == p-1 (mod p^2)`.

Formalized: for every odd prime `p`, `(p-1)! == -1 (mod p^2)` holds if and only if
`Sum_{k=1..p-1} k^(p-1) == p-1 (mod p^2)`, both congruences taken in `ℤ`.
-/

namespace OMA.S_oeis_a007540

open Finset

theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 →
    (((p - 1).factorial : ℤ) ≡ -1 [ZMOD (p : ℤ) ^ 2] ↔
      (∑ k ∈ Ico 1 p, (k : ℤ) ^ (p - 1)) ≡ (p : ℤ) - 1 [ZMOD (p : ℤ) ^ 2]) := by
  sorry

end OMA.S_oeis_a007540
