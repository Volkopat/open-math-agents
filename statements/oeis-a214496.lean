import Mathlib

/-!
# A214496: twin primes (3^n + k)*3^n - 1, (3^n + k)*3^n + 1

Source: https://oeis.org/A214496

A214496 (offset 1): `a(n)` is the smallest `k > 0` such that `(3^n+k)*3^n - 1` and
`(3^n+k)*3^n + 1` are a twin prime pair: 1, 3, 3, 7, 21, 29, 113, 31, 61, 13, …

Conjecture (Pierre CAMI, Jul 20 2012): there is always one such `k` for each `n > 0`.

The conjecture is stated as: for every `n > 0` there is a `k > 0` such that both
`(3^n+k)*3^n - 1` and `(3^n+k)*3^n + 1` are prime (two primes differing by 2).

Conventions: everything is in `ℕ`; the subtraction of 1 is exact because `(3^n+k)*3^n ≥ 1`.
-/

namespace OMA.S_oeis_a214496

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ k : ℕ, 0 < k ∧ Nat.Prime ((3 ^ n + k) * 3 ^ n - 1) ∧
        Nat.Prime ((3 ^ n + k) * 3 ^ n + 1) := by
  sorry

end OMA.S_oeis_a214496
