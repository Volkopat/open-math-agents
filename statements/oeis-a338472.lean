import Mathlib

/-!
# A338472: (1 + Sum_{even k < p} 2*k^(p-1))/p is an integer iff p is an odd prime

Source: https://oeis.org/A338472

A338472 (offset 1): `(1 + Sum_{k(even)=2..p-1} 2*k^(p-1))/p` as `p` runs through the odd primes:
3, 109, 14519, 2024592291, 1536463613637, …  For example for `p = 3` the value is
`(1 + 2*2^2)/3 = 3`.

Conjecture (Davide Rotondo, Oct 29 2020): `(1 + Sum_{k(even)=2..p-1} 2*k^(p-1))/p` is an integer
iff `p` is an odd prime.

Conventions:
- The quotient is an integer exactly when `p` divides `1 + Sum_{k even, 2 ≤ k ≤ p-1} 2*k^(p-1)`.
  The even `k` in `2..p-1` are written as `k = 2*j` with `j ≥ 1` and `2*j ≤ p - 1`, i.e.
  `j` in `Finset.Icc 1 ((p - 1) / 2)`.
- The entry does not say over which `p` the equivalence ranges. It is stated here for all
  integers `p ≥ 2`. (For `p = 1` the quotient `1/1` is an integer although `1` is not a prime,
  so `p = 1` has to be excluded; for `p = 2` the sum is empty and `1/2` is not an integer.)
- An odd prime is a prime different from 2. Everything is in `ℕ`; `p - 1` is exact for `p ≥ 2`.
-/

namespace OMA.S_oeis_a338472

theorem main :
    ∀ p : ℕ, 2 ≤ p →
      (p ∣ 1 + ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), 2 * (2 * j) ^ (p - 1) ↔
        (Nat.Prime p ∧ p ≠ 2)) := by
  sorry

end OMA.S_oeis_a338472
