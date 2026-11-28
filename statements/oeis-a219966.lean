import Mathlib

/-!
# A219966: n = p + q + (n mod 2)*q with q ≤ n/2 and p, q, q + 6 all prime

Source: https://oeis.org/A219966

A219966 (offset 1): `a(n)` is the number of ways to write `n = p + q + (n mod 2)*q` with
`q ≤ n/2` and `p`, `q`, `q + 6` all prime. So an even `n` is written as `p + q` and an odd `n`
as `p + 2q`. For example `a(19) = 1` from `19 = 5 + 2*7`, and `a(20) = 1` from `20 = 13 + 7`.

Conjecture (Zhi-Wei Sun, Dec 02 2012): `a(n) > 0` for all `n > 11`. The entry notes that this is
stronger than Goldbach's conjecture and Lemoine's conjecture.

Since `a(n)` counts the pairs of primes `(p, q)` with `n = p + q + (n mod 2)*q`, `q ≤ n/2` and
`q + 6` prime, `a(n) > 0` says exactly that such a pair exists, and the conjecture is stated in
that form.

Conventions: everything is in `ℕ`; `n mod 2` is `n % 2`, and the real inequality `q ≤ n/2` is
written as `2*q ≤ n`.
-/

namespace OMA.S_oeis_a219966

theorem main :
    ∀ n : ℕ, 11 < n →
      ∃ p q : ℕ, p + q + (n % 2) * q = n ∧ 2 * q ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (q + 6) := by
  sorry

end OMA.S_oeis_a219966
