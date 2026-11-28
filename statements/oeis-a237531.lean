import Mathlib

/-!
# A237531: 0 < k < n/2 with phi(k*(n-k)) - 1 and phi(k*(n-k)) + 1 both prime

Source: https://oeis.org/A237531

A237531 (offset 1): `a(n) = |{0 < k < n/2 : phi(k*(n-k)) - 1 and phi(k*(n-k)) + 1 are both
prime}|`, where `phi` is Euler's totient function. For example `a(12) = 1` since `12 = 3 + 9`
with `phi(3*9) - 1 = 17` and `phi(3*9) + 1 = 19` both prime.

Conjecture (Zhi-Wei Sun, Feb 09 2014): `a(n) > 0` for all `n > 5`. The entry notes that this
implies the twin prime conjecture.

Since `a(n)` counts the `0 < k < n/2` with `phi(k*(n-k)) - 1` and `phi(k*(n-k)) + 1` both prime,
`a(n) > 0` says exactly that such a `k` exists, and the conjecture is stated in that form.

Conventions:
- `phi` is `Nat.totient`. The real inequality `k < n/2` is written as `2*k < n`.
- Everything is in `ℕ`. The subtraction `n - k` is exact because `2*k < n`, and
  `phi(k*(n-k)) - 1` is exact because the totient of a positive integer is positive.
-/

namespace OMA.S_oeis_a237531

theorem main :
    ∀ n : ℕ, 5 < n →
      ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ Nat.Prime (Nat.totient (k * (n - k)) - 1) ∧
        Nat.Prime (Nat.totient (k * (n - k)) + 1) := by
  sorry

end OMA.S_oeis_a237531
