import Mathlib

/-!
# A240233: smallest prime p such that p + 6n and p + 12n are both prime

Source: https://oeis.org/A240233

A240233 (offset 1): `a(n)` is the smallest prime number such that both `a(n) + 6n` and
`a(n) + 12n` are prime numbers, so that `a(n)`, `a(n) + 6n`, `a(n) + 12n` are three primes in
arithmetic progression with common difference `6n`: 5, 5, 5, 5, 7, 7, 5, 5, 5, 7, …  For example
`a(1) = 5` from `5, 11, 17`, and `a(13) = 11` from `11, 89, 167`.

Conjecture (Lei Zhou, Apr 02 2014): `a(n)` is defined for all `n > 0`.

`a(n)` is defined exactly when some prime `p` has `p + 6n` and `p + 12n` both prime, so the
conjecture is stated as the existence of such a prime for every `n > 0`.

Conventions: everything is in `ℕ`; `n` ranges over the positive integers (offset 1).
-/

namespace OMA.S_oeis_a240233

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 6 * n) ∧ Nat.Prime (p + 12 * n) := by
  sorry

end OMA.S_oeis_a240233
