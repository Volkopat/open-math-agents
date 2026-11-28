import Mathlib

/-!
# A220956: (C(2n,n) - C(2n-2,n-1)) mod n^2 = n + 2 exactly for odd primes

Source: https://oeis.org/A220956

A220956 (offset 1): `a(n) = (binomial(2n, n) - binomial(2n-2, n-1)) (mod n^2) - n - 2`:
-3, -4, 0, -4, 0, 16, 0, 20, 18, 24, 0, -10, 0, …  For example `a(8) = 20` since
`C(16,8) - C(14,7) = 12870 - 3432 = 9438 ≡ 30 (mod 64)` and `30 - 8 - 2 = 20`.

Conjecture (Gary Detlefs and Robert G. Wilson v, Feb 20 2013): `a(n) = 0` iff `n` is an odd
prime.

Conventions:
- `a(n) = 0` means that the least nonnegative residue of `C(2n,n) - C(2n-2,n-1)` modulo `n^2`
  equals `n + 2`; this is stated with `%` in `ℕ`, which avoids the negative values of `a`.
- The subtraction of binomial coefficients is exact, since `C(2n-2, n-1) ≤ C(2n, n)`, and
  `2*n - 2`, `n - 1` are exact for `n ≥ 1`.
- An odd prime is a prime different from 2. `n` ranges over the positive integers (offset 1).
-/

namespace OMA.S_oeis_a220956

theorem main :
    ∀ n : ℕ, 0 < n →
      ((((2 * n).choose n - (2 * n - 2).choose (n - 1)) % n ^ 2 = n + 2) ↔
        (Nat.Prime n ∧ n ≠ 2)) := by
  sorry

end OMA.S_oeis_a220956
