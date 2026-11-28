import Mathlib

/-!
# A294646: (1/2)^(2n) mod (2n+1) is never 2, 2n or 2n-2

Source: https://oeis.org/A294646

A294646 (offset 1): `a(n) = (1/2)^(2*n) mod (2*n+1)`, that is, the smallest `k > 0` such that
`k*2^(2*n) ≡ 1 (mod 2*n+1)`: 1, 1, 1, 7, 1, 1, 4, 1, 1, 16, 1, 11, 25, …  The entry notes that
`1 ≤ a(n) ≤ 2*n` and that `a(n)` is always coprime to `2*n+1`.

Conjecture (Robert Israel and Thomas Ordowski, Nov 05 2017): `a(n)` is never 2 or `2*n` or
`2*n - 2`.

Conventions:
- `a(n)` is the unique `k` with `1 ≤ k ≤ 2n` and `k*4^n ≡ 1 (mod 2n+1)` (the inverse of the unit
  `4^n` modulo `2n+1`). For a value `c` with `1 ≤ c ≤ 2n`, the claim `a(n) ≠ c` is therefore
  the same as `c*4^n ≢ 1 (mod 2n+1)`.
- The statement is, for every `n ≥ 1` (offset 1): none of `2`, `2n`, `2n - 2` multiplied by
  `4^n` is congruent to `1` modulo `2n+1`. For `n ≥ 1` the values `2` and `2n` lie in the range
  `1..2n`; the value `2n - 2` lies in that range for `n ≥ 2`, and for `n = 1` it is `0`, where
  both `a(1) ≠ 0` and `0*4 ≢ 1 (mod 3)` hold trivially.
- Everything is in `ℕ`, with `Nat.ModEq`; `2*n - 2` is an exact subtraction for `n ≥ 1`.
-/

namespace OMA.S_oeis_a294646

theorem main :
    ∀ n : ℕ, 0 < n →
      ¬ (2 * 4 ^ n ≡ 1 [MOD 2 * n + 1]) ∧
      ¬ (2 * n * 4 ^ n ≡ 1 [MOD 2 * n + 1]) ∧
      ¬ ((2 * n - 2) * 4 ^ n ≡ 1 [MOD 2 * n + 1]) := by
  sorry

end OMA.S_oeis_a294646
