import Mathlib

/-!
# A218797: 2n - 1 = p + q + r with p, q, r and p^2 + q^2 + r^2 all prime

Source: https://oeis.org/A218797

A218797 (offset 1): `a(n)` is the number of ways to write `2n - 1` as `p + q + r` with
`p ≤ q ≤ r` and `p`, `q`, `r`, `p^2 + q^2 + r^2` all prime. For example `a(7) = 2` since
`13 = 3 + 3 + 7 = 3 + 5 + 5`, and both `3^2 + 3^2 + 7^2 = 67` and `3^2 + 5^2 + 5^2 = 59` are
prime.

Conjecture (Zhi-Wei Sun, Nov 05 2012): `a(n) > 0` for all `n = 1715, 1716, …`. The entry notes
that this is stronger than the weak Goldbach conjecture, that it has been verified for `n` up to
500,000, and that the `0 < n < 1715` with `a(n) = 0` are 1, 2, 3, 5, 10, 46, 126, 129, 154, 201,
385, 426, 475, 1714.

Since `a(n)` counts the triples of primes `p ≤ q ≤ r` with `p + q + r = 2n - 1` and
`p^2 + q^2 + r^2` prime, `a(n) > 0` says exactly that such a triple exists, and the conjecture
is stated in that form.

Conventions: everything is in `ℕ`; the equation is written as `p + q + r + 1 = 2*n` to avoid
subtraction.
-/

namespace OMA.S_oeis_a218797

theorem main :
    ∀ n : ℕ, 1715 ≤ n →
      ∃ p q r : ℕ, p ≤ q ∧ q ≤ r ∧ p + q + r + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime r ∧ Nat.Prime (p ^ 2 + q ^ 2 + r ^ 2) := by
  sorry

end OMA.S_oeis_a218797
