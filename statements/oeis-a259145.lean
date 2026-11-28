import Mathlib

/-!
# A259145: numbers k such that k^2 - phi(k) is prime are cyclic numbers

Source: https://oeis.org/A259145

A259145 (offset 1): the numbers `k` such that `k^2 - phi(k)` is prime, where `phi` is Euler's
totient function A000010: 2, 3, 7, 13, 33, 35, 65, 67, 77, 79, 91, 133, …  For example 33 is a
term since `phi(33) = 20` and `33^2 - 20 = 1069` is prime.

Conjecture (Carlos Eduardo Olivieri, Jun 19 2015): `a(n)` is a cyclic number (see A003277) for
all `n`.

Conventions:
- A cyclic number (A003277) is a positive integer `k` with `gcd(k, phi(k)) = 1` (equivalently,
  every group of order `k` is cyclic).
- The terms of the sequence are exactly the `k` with `k^2 - phi(k)` prime, so the conjecture is
  stated as: for every `k`, if `k^2 - phi(k)` is prime then `gcd(k, phi(k)) = 1`.
- `phi` is `Nat.totient`. Everything is in `ℕ`; the subtraction is exact because
  `phi(k) ≤ k ≤ k^2`. For `k = 0` and `k = 1` the number `k^2 - phi(k)` is `0`, not a prime, so
  these values do not arise.
-/

namespace OMA.S_oeis_a259145

theorem main :
    ∀ k : ℕ, Nat.Prime (k ^ 2 - Nat.totient k) → Nat.Coprime k (Nat.totient k) := by
  sorry

end OMA.S_oeis_a259145
