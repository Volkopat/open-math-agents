import Mathlib

/-!
# A212488: twin primes (5^n - k)*5^n - 1, (5^n - k)*5^n + 1

Source: https://oeis.org/A212488

A212488 (offset 1): `a(n)` is the smallest `k > 0` such that `(5^n-k)*5^n - 1` and
`(5^n-k)*5^n + 1` are a twin prime pair, or 0 if no such `k` exists:
0, 1, 11, 1, 17, 85, 17, 25, 71, 25, …

Conjecture (Pierre CAMI, Jul 18 2012): there is always one such `k` if `n > 1`.

The conjecture is stated as: for every `n > 1` there is a `k > 0` such that both
`(5^n-k)*5^n - 1` and `(5^n-k)*5^n + 1` are prime (two primes differing by 2).

Conventions: everything is in `ℕ`. The truncated subtractions are harmless: if `k ≥ 5^n` then
`(5^n - k)*5^n` is `0` in `ℕ`, giving the non-primes `0` and `1`, just as the integer values
`(5^n-k)*5^n ± 1` are not a pair of primes when `k ≥ 5^n`. For `k < 5^n` all subtractions are
exact.
-/

namespace OMA.S_oeis_a212488

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ k : ℕ, 0 < k ∧ Nat.Prime ((5 ^ n - k) * 5 ^ n - 1) ∧
        Nat.Prime ((5 ^ n - k) * 5 ^ n + 1) := by
  sorry

end OMA.S_oeis_a212488
