import Mathlib

/-!
# A303543: sums of two squares and two Catalan numbers

Source: https://oeis.org/A303543

A303543 (offset 1): `a(n)` is the number of ways to write `n` as `a^2 + b^2 + C(k) + C(m)` with
`0 ≤ a ≤ b` and `0 < k ≤ m`, where `C(k)` denotes the Catalan number `binomial(2k,k)/(k+1)`:
0, 1, 2, 3, 2, 3, 4, 4, 2, 3, …  For example `2 = 0^2 + 0^2 + C(1) + C(1)`.

Conjecture (Zhi-Wei Sun, Apr 25 2018): `a(n) > 0` for all `n > 1`. In other words, any integer
`n > 1` can be written as the sum of two squares and two Catalan numbers. The entry notes that
this has been verified for all `n = 2..10^9`.

The conjecture is stated as the existence of `a, b, k, m` with `k, m > 0`, as in the sequence
definition. The ordering conditions `a ≤ b` and `k ≤ m` only remove double counting and do not
affect existence, so they are omitted.

Conventions: `C(k)` is Mathlib's `catalan k`. The indices `k, m` are positive, as in the entry;
since `C(0) = C(1) = 1`, this is the same set of Catalan numbers as with `k, m ≥ 0`.
-/

namespace OMA.S_oeis_a303543

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ a b k m : ℕ, 0 < k ∧ 0 < m ∧ a ^ 2 + b ^ 2 + catalan k + catalan m = n := by
  sorry

end OMA.S_oeis_a303543
