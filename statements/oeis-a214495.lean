import Mathlib

/-!
# A214495: twin primes (3^n - k)*3^n - 1, (3^n - k)*3^n + 1

Source: https://oeis.org/A214495

A214495 (offset 1): `a(n)` is the smallest `k > 0` such that `(3^n-k)*3^n - 1` and
`(3^n-k)*3^n + 1` are a twin prime pair: 1, 1, 11, 19, 7, 1, 23, 31, 53, 49, …

Conjecture (Pierre CAMI, Jul 19 2012): there is always one such `k(n)` for each `n > 0`.

The conjecture is stated as: for every `n > 0` there is a `k > 0` such that both
`(3^n-k)*3^n - 1` and `(3^n-k)*3^n + 1` are prime (two primes differing by 2).

Conventions: everything is in `ℕ`. The truncated subtractions are harmless: if `k ≥ 3^n` then
`(3^n - k)*3^n` is `0` in `ℕ`, giving the non-primes `0` and `1`, just as the integer values
`(3^n-k)*3^n ± 1` are not a pair of primes when `k ≥ 3^n`. For `k < 3^n` all subtractions are
exact.
-/

namespace OMA.S_oeis_a214495

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ k : ℕ, 0 < k ∧ Nat.Prime ((3 ^ n - k) * 3 ^ n - 1) ∧
        Nat.Prime ((3 ^ n - k) * 3 ^ n + 1) := by
  sorry

end OMA.S_oeis_a214495
