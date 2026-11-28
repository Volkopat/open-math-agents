import Mathlib

/-!
# A232269: 2n + 1 = x + y with x^3 + y^2 and x^2 + y^2 both prime

Source: https://oeis.org/A232269

A232269 (offset 1): `a(n)` is the number of ways to write `2*n + 1 = x + y` (`x, y > 0`) with
`x^3 + y^2` and `x^2 + y^2` both prime. For example `a(10) = 1` since `21 = 1 + 20` with
`1^2 + 20^2 = 1^3 + 20^2 = 401` prime.

Conjecture (Zhi-Wei Sun, Nov 22 2013): `a(n) > 0` for all `n > 0`. Also, any odd integer greater
than one can be written as `x + y` (`0 < x < y`) with `x^3 + y^2` prime.

Both sentences of the conjecture are stated, as a conjunction. Since `a(n)` counts the pairs of
positive integers `(x, y)` with `x + y = 2n + 1` and `x^3 + y^2`, `x^2 + y^2` both prime, the
first sentence says exactly that such a pair exists.

Conventions: everything is in `ℕ`. In the second part the odd integers greater than one are
written as `2*n + 1` with `n > 0`.
-/

namespace OMA.S_oeis_a232269

theorem main :
    (∀ n : ℕ, 0 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = 2 * n + 1 ∧ Nat.Prime (x ^ 3 + y ^ 2) ∧
        Nat.Prime (x ^ 2 + y ^ 2)) ∧
    (∀ n : ℕ, 0 < n →
      ∃ x y : ℕ, 0 < x ∧ x < y ∧ x + y = 2 * n + 1 ∧ Nat.Prime (x ^ 3 + y ^ 2)) := by
  sorry

end OMA.S_oeis_a232269
