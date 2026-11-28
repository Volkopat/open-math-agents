import Mathlib

/-!
# A252503: smallest prime p such that Phi_n(p) is also prime

Source: https://oeis.org/A252503

A252503 (offset 1): `a(n)` is the smallest prime `p` such that `Phi_n(p)` is also prime, where
`Phi_n` is the `n`-th cyclotomic polynomial, or 0 if no such `p` exists:
3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 2, 2, 2, 2, 2, 2, 7, 2, 11, …

Conjecture (Eric Chen, Dec 18 2014): `a(n) > 0` for all `n != 2^k (k > 5)`. That is, for every
positive integer `n` that is not a power of two `2^k` with `k > 5`, there is a prime `p` such
that `Phi_n(p)` is prime. (The entry remarks that if `n` is a power of 2 and `Phi_n(2)` is not
prime, then `a(n) = 0`; for example `a(64) = 0`.)

Conventions:
- `a(n) > 0` means that a prime `p` with `Phi_n(p)` prime exists; the value 0 is only the entry's
  marker for the case that none does.
- `Phi_n` is `Polynomial.cyclotomic n ℤ`, evaluated at the integer `p`. Its value is asked to be
  equal to a prime natural number `q`.
- The excluded indices are the `n = 2^k` with `k > 5` (64, 128, 256, …); the powers of two
  `1, 2, 4, 8, 16, 32` are not excluded. `n` ranges over the positive integers (offset 1).
-/

namespace OMA.S_oeis_a252503

theorem main :
    ∀ n : ℕ, 0 < n → (∀ k : ℕ, 5 < k → n ≠ 2 ^ k) →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
        (Polynomial.cyclotomic n ℤ).eval (p : ℤ) = (q : ℤ) := by
  sorry

end OMA.S_oeis_a252503
