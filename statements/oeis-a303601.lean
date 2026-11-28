import Mathlib

/-!
# A303601: sums of two triangular numbers and two Bell numbers

Source: https://oeis.org/A303601

A303601 (offset 1): `a(n)` is the number of ways to write `n` as
`a*(a+1)/2 + b*(b+1)/2 + Bell(k) + Bell(m)` with `0 ≤ a ≤ b` and `0 < k ≤ m`, where `Bell(k)`
denotes the `k`-th Bell number A000110(k): 0, 1, 2, 3, 3, 4, 4, 5, 5, 6, …  For example
`2 = 0*(0+1)/2 + 0*(0+1)/2 + Bell(1) + Bell(1)`.

Conjecture (Zhi-Wei Sun, Apr 26 2018): `a(n) > 0` for all `n > 1`. In other words, any integer
`n > 1` can be expressed as the sum of two triangular numbers and two Bell numbers. The entry
notes that this has been verified for all `n = 2..7*10^8`.

The conjecture is stated as the existence of `a, b, k, m` with `k, m > 0`, as in the sequence
definition. The ordering conditions `a ≤ b` and `k ≤ m` only remove double counting and do not
affect existence, so they are omitted.

Conventions: `Bell(k)` is Mathlib's `Nat.bell k` (1, 1, 2, 5, 15, 52, … for `k = 0, 1, 2, …`).
The indices `k, m` are positive, as in the entry; since `Bell(0) = Bell(1) = 1`, this is the
same set of Bell numbers as with `k, m ≥ 0`. The triangular number `a*(a+1)/2` uses
natural-number division, which is exact.
-/

namespace OMA.S_oeis_a303601

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ a b k m : ℕ, 0 < k ∧ 0 < m ∧
        a * (a + 1) / 2 + b * (b + 1) / 2 + Nat.bell k + Nat.bell m = n := by
  sorry

end OMA.S_oeis_a303601
