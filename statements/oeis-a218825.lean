import Mathlib

/-!
# A218825: 2n - 1 = p + 2q with p, q and p^2 + 60q^2 all prime

Source: https://oeis.org/A218825

A218825 (offset 1): `a(n)` is the number of ways to write `2n - 1` as `p + 2q` with `p`, `q` and
`p^2 + 60*q^2` all prime. For example `a(10) = 1`, from `19 = 13 + 2*3` with
`13^2 + 60*3^2 = 709` prime.

Conjecture (Zhi-Wei Sun, Nov 07 2012): `a(n) > 0` for all `n > 8`. The entry notes that this is
stronger than Lemoine's conjecture and that it has been verified for `2n - 1` up to `10^9`
(Mauro Fiorentini, Jul 20 2023).

Since `a(n)` counts the pairs of primes `(p, q)` with `p + 2q = 2n - 1` and `p^2 + 60q^2` prime,
`a(n) > 0` says exactly that such a pair exists, and the conjecture is stated in that form. The
general conjecture (with `4*(2^n - 1)` in place of 60) and the further guess listed afterwards
in the entry are separate claims and are not part of this statement.

Conventions: everything is in `ℕ`; the equation is written as `p + 2*q + 1 = 2*n` to avoid
subtraction.
-/

namespace OMA.S_oeis_a218825

theorem main :
    ∀ n : ℕ, 8 < n →
      ∃ p q : ℕ, p + 2 * q + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (p ^ 2 + 60 * q ^ 2) := by
  sorry

end OMA.S_oeis_a218825
