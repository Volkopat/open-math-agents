import Mathlib

/-!
# A387790: n = S(i) + S(j) + 2*S(k) with S(k) the sum of the first k primes

Source: https://oeis.org/A387790

A387790 (offset 1): `a(n)` is the number of ways to write `n` as `S(i) + S(j) + 2*S(k)`, where
`i, j, k` are positive integers with `i ≥ j`, and `S(k)` is the sum of the first `k` primes:
0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, …  For example `a(70) = 1` with
`70 = 58 + 2 + 2*5 = S(7) + S(1) + 2*S(2)`.

Conjecture (Zhi-Wei Sun, Oct 09 2025): `a(n) > 0` for all `n ≥ 5340`. In other words, each
integer `n ≥ 5340` is a sum of four elements of the set `{Sum_{k=1..m} prime(k) : m = 1, 2, …}`
two of which are equal. The entry notes that this has been verified for `n ≤ 3*10^5`.

Since `a(n)` counts the triples `(i, j, k)` of positive integers with `i ≥ j` and
`S(i) + S(j) + 2*S(k) = n`, `a(n) > 0` says exactly that such a triple exists, and the
conjecture is stated in that form. The ordering condition `i ≥ j` only removes double counting
and does not affect existence, so it is omitted.

Conventions: `S k` is the sum of the first `k` primes,
`∑ i ∈ Finset.range k, Nat.nth Nat.Prime i` (`S 1 = 2`, `S 2 = 5`, `S 3 = 10`, …), and
`i, j, k` are positive.
-/

namespace OMA.S_oeis_a387790

/-- The sum of the first `k` primes. -/
noncomputable def S (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i

theorem main :
    ∀ n : ℕ, 5340 ≤ n →
      ∃ i j k : ℕ, 0 < i ∧ 0 < j ∧ 0 < k ∧ S i + S j + 2 * S k = n := by
  sorry

end OMA.S_oeis_a387790
