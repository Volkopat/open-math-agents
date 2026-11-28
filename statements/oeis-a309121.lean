import Mathlib

/-!
# A309121: a prime in every interval [(j^2 + 3j - 2)/2, j(j + 5)/2]

Source: https://oeis.org/A309121

A309121 (offset 1): `a(n)` gives the number of primes in the interval
`I_j = [(j^2 + 3*j - 2)/2, j*(j + 5)/2] = [A034856(j), A095998(j)]`, for `j ≥ 1`:
2, 2, 1, 2, 2, 2, 2, 2, 3, 3, …  The intervals are `I_1 = [1, 2, 3]`, `I_2 = [4, 5, 6, 7]`, …,
and the length of `I_n` is `n + 2`.

Conjecture (Wolfdieter Lang, Jul 13 2019): `a(n) ≥ 1`. That is, every interval `I_j` with
`j ≥ 1` contains a prime.

Conventions: everything is in `ℕ`. The divisions by 2 are exact, because `j^2 + 3j - 2` and
`j*(j+5)` are even, and for `j ≥ 1` the subtraction `j^2 + 3*j - 2` is exact. The intervals are
closed at both ends.
-/

namespace OMA.S_oeis_a309121

theorem main :
    ∀ j : ℕ, 1 ≤ j →
      ∃ p : ℕ, Nat.Prime p ∧ (j ^ 2 + 3 * j - 2) / 2 ≤ p ∧ p ≤ j * (j + 5) / 2 := by
  sorry

end OMA.S_oeis_a309121
