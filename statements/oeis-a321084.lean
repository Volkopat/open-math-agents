import Mathlib

/-!
# A321084: 1 + Sum_{k=1..n} 2^(prime(k)-1) is prime iff it divides 2^S(n) - 1

Source: https://oeis.org/A321084

A321084 (offset 1): the primes `prime(n)` such that `1 + Sum_{k=1..n} 2^(prime(k)-1)` is prime:
2, 3, 5, 19, 2039, 2879, …  For example 5 is a term since
`1 + 2^(2-1) + 2^(3-1) + 2^(5-1) = 23` is prime.

Conjecture (Thomas Ordowski, Oct 27 2018): let `S(n) = Sum_{k=1..n} 2^(prime(k)-1)`. Then
`q(n) = 1 + S(n)` is prime if and only if `2^S(n) ≡ 1 (mod q(n))`.

Conventions:
- `prime(k)` is the `k`-th prime with `prime(1) = 2`; the sum over `k = 1..n` is written over
  `i` in `Finset.range n` with `prime(i+1) = Nat.nth Nat.Prime i`.
- Everything is in `ℕ`, the congruence is `Nat.ModEq`, and `prime(k) - 1` is an exact
  subtraction. `n` ranges over the positive integers.
-/

namespace OMA.S_oeis_a321084

/-- `S(n) = Sum_{k=1..n} 2^(prime(k)-1)`. -/
noncomputable def S (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 2 ^ (Nat.nth Nat.Prime i - 1)

theorem main :
    ∀ n : ℕ, 0 < n → (Nat.Prime (1 + S n) ↔ 2 ^ S n ≡ 1 [MOD 1 + S n]) := by
  sorry

end OMA.S_oeis_a321084
