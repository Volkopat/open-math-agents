import Mathlib

/-!
# A372457: least k with k^2 + k + 1 divisible by the n-th power of a prime

Source: https://oeis.org/A372457

A372457 (offset 1): `a(n)` is the least `k` such that `k^2 + k + 1` is divisible by the `n`-th
power of a prime: 1, 18, 18, 1047, 1353, 34967, 82681, …  For example `a(4) = 1047` because
`1047^2 + 1047 + 1 = 1097257` is divisible by `7^4`.

The entry notes that for `n > 1` the prime is in A002476 (primes of the form `6m+1`).

Conjecture (Robert Israel, May 01 2024): it is always 7. That is, for `n > 1` the prime whose
`n`-th power divides `a(n)^2 + a(n) + 1` is 7.

Conventions:
- `a(n)` is the least element of the set of natural numbers `k` for which some prime `p` has
  `p^n ∣ k^2 + k + 1`. (The value `k = 0` is never in this set, since `0^2 + 0 + 1 = 1` has no
  prime divisor; for `n = 1` the least element is `1`, where `3` divides `1^2 + 1 + 1`.)
- The statement is: for every `n > 1`, if `k` is the least natural number such that
  `k^2 + k + 1` is divisible by the `n`-th power of some prime (`IsLeast`), then
  `7^n ∣ k^2 + k + 1`.
-/

namespace OMA.S_oeis_a372457

theorem main :
    ∀ n k : ℕ, 1 < n →
      IsLeast {k : ℕ | ∃ p : ℕ, Nat.Prime p ∧ p ^ n ∣ k ^ 2 + k + 1} k →
      7 ^ n ∣ k ^ 2 + k + 1 := by
  sorry

end OMA.S_oeis_a372457
