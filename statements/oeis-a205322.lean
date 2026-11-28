import Mathlib

/-!
# A205322: twin primes (2^n - k)*2^n - 1, (2^n - k)*2^n + 1

Source: https://oeis.org/A205322

A205322 (offset 1): `a(n)` is the smallest `k ≥ 0` such that `(2^n-k)*2^n - 1` and
`(2^n-k)*2^n + 1` are a twin prime pair; or `-1` if no such `k` exists:
0, 1, -1, 1, 26, 22, 8, 28, 47, 16, …

Conjecture (Pierre CAMI, Jul 14 2012): there is always at least one `k ≥ 0` unless `n = 3`.

The statement is the equivalence, for every `n ≥ 1`: a `k ≥ 0` with both `(2^n-k)*2^n - 1` and
`(2^n-k)*2^n + 1` prime exists if and only if `n ≠ 3`. (That no such `k` exists for `n = 3` is a
finite computation, recorded in the sequence as `a(3) = -1`; the open content is the existence
for all other `n`.)

Conventions: everything is in `ℕ`, with `k` any natural number. The truncated subtractions are
harmless: if `k ≥ 2^n` then `(2^n - k)*2^n` is `0` in `ℕ`, giving the non-primes `0` and `1`,
just as the integer values `(2^n-k)*2^n ± 1` are not a pair of primes when `k ≥ 2^n`. For
`k < 2^n` all subtractions are exact.
-/

namespace OMA.S_oeis_a205322

theorem main :
    ∀ n : ℕ, 0 < n →
      ((∃ k : ℕ, Nat.Prime ((2 ^ n - k) * 2 ^ n - 1) ∧ Nat.Prime ((2 ^ n - k) * 2 ^ n + 1)) ↔
        n ≠ 3) := by
  sorry

end OMA.S_oeis_a205322
