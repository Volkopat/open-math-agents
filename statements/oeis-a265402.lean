import Mathlib

/-!
# A265402: gcd_{k=1..n-1} C(2n, 2k) = n exactly for primes n with 2n-1 not a prime power

Source: https://oeis.org/A265402

A265402 (offset 1): the fixed points of A265388, i.e. the numbers `n` for which
`gcd_{k=1..n-1} binomial(2*n, 2*k) = n`: 11, 17, 23, 29, 43, 47, 53, 59, 67, 71, …

The entry (Chai Wah Wu, Oct 28 2026) notes that if `p` is prime, then `p` is a term if and only
if `2p - 1` is not a prime power, and states:

Conjecture (Chai Wah Wu, Oct 28 2026): `n` is a term if and only if `n` is prime and `2n - 1`
is not a prime power.

Conventions:
- The gcd of the binomial coefficients `C(2n, 2k)` for `1 ≤ k ≤ n-1` is `Finset.gcd` over
  `Finset.Icc 1 (n - 1)`.
- A prime power is `p^k` with `p` prime and `k ≥ 1` (Mathlib's `IsPrimePow`), so a prime counts
  as a prime power.
- `n` ranges over the positive integers. (For `n = 1` the gcd is over the empty set and equals
  `0`, not `1`, and `1` is not prime, so both sides are false.)
-/

namespace OMA.S_oeis_a265402

theorem main :
    ∀ n : ℕ, 0 < n →
      ((Finset.Icc 1 (n - 1)).gcd (fun k => (2 * n).choose (2 * k)) = n ↔
        (Nat.Prime n ∧ ¬ IsPrimePow (2 * n - 1))) := by
  sorry

end OMA.S_oeis_a265402
