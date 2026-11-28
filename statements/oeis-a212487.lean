import Mathlib

/-!
# A212487: twin primes (5^n + k)*5^n - 1, (5^n + k)*5^n + 1

Source: https://oeis.org/A212487

A212487 (offset 1): `a(n)` is the smallest `k > 0` such that `(5^n+k)*5^n - 1` and
`(5^n+k)*5^n + 1` are a twin prime pair: 1, 17, 85, 47, 19, 71, 955, 815, 223, 269, …

Conjecture (Pierre CAMI, Jul 18 2012): there is always one such `k` for `n > 0`.

The conjecture is stated as: for every `n > 0` there is a `k > 0` such that both
`(5^n+k)*5^n - 1` and `(5^n+k)*5^n + 1` are prime (two primes differing by 2).

Conventions: everything is in `ℕ`; the subtraction of 1 is exact because `(5^n+k)*5^n ≥ 1`.
-/

namespace OMA.S_oeis_a212487

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ k : ℕ, 0 < k ∧ Nat.Prime ((5 ^ n + k) * 5 ^ n - 1) ∧
        Nat.Prime ((5 ^ n + k) * 5 ^ n + 1) := by
  sorry

end OMA.S_oeis_a212487
