import Mathlib

/-!
# A218654: n = x + y with 0 < x ≤ y and x^2 + 3xy + y^2 prime

Source: https://oeis.org/A218654

A218654 (offset 1): `a(n)` is the number of ways to write `n` as `x + y` with `0 < x ≤ y` and
`x^2 + 3xy + y^2` prime: 0, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, …

Conjecture (Zhi-Wei Sun, Nov 03 2012): `a(n) > 0` for all `n = 2, 3, 4, …`.

Since `a(n)` counts the pairs `(x, y)` with `x + y = n`, `0 < x ≤ y` and `x^2 + 3xy + y^2` prime,
`a(n) > 0` says exactly that such a pair exists, and the conjecture is stated in that form.
The entry also records a further conjecture of Sun on the limit of a ratio of sums over primes
`p ≡ ±1 (mod 5)`; that is a separate claim and is not part of this statement.

Conventions: everything is in `ℕ`; `x` and `y` are positive because `0 < x ≤ y`.
-/

namespace OMA.S_oeis_a218654

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x ^ 2 + 3 * x * y + y ^ 2) := by
  sorry

end OMA.S_oeis_a218654
