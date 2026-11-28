import Mathlib

/-!
# A291624: n = x^2 + y^2 + z^2 + w^2 with p = x + 2y + 5z, p - 2 and p + 4 all prime

Source: https://oeis.org/A291624

A291624 (offset 1): `a(n)` is the number of ways to write `n` as `x^2 + y^2 + z^2 + w^2` with
`x, y, z, w` nonnegative integers such that `p = x + 2*y + 5*z`, `p - 2` and `p + 4` are all
prime: 0, 1, 1, 0, 1, 3, 1, 0, 1, 2, 2, 0, …  For example `a(2) = 1` since
`2 = 0^2 + 1^2 + 1^2 + 0^2` with `0 + 2*1 + 5*1 = 7`, `7 - 2 = 5` and `7 + 4 = 11` all prime.

Conjecture (Zhi-Wei Sun, Aug 28 2017): `a(n) > 0` for all `n > 1` not divisible by 4.

Since `a(n)` counts the quadruples `(x, y, z, w)` of nonnegative integers satisfying the stated
conditions, `a(n) > 0` says exactly that such a quadruple exists, and the conjecture is stated
in that form.

Conventions: `x, y, z, w` range over `ℕ`. The subtraction `p - 2` is truncated only when
`p < 2`, in which case `p` itself is not prime, so the two readings agree.
-/

namespace OMA.S_oeis_a291624

theorem main :
    ∀ n : ℕ, 1 < n → ¬ 4 ∣ n →
      ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ Nat.Prime (x + 2 * y + 5 * z) ∧
        Nat.Prime (x + 2 * y + 5 * z - 2) ∧ Nat.Prime (x + 2 * y + 5 * z + 4) := by
  sorry

end OMA.S_oeis_a291624
