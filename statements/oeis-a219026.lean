import Mathlib

/-!
# A219026: primes p ≤ n with 2n - p and 2n + p - 2 both prime

Source: https://oeis.org/A219026

A219026 (offset 1): `a(n)` is the number of primes `p ≤ n` such that `2n - p` and `2n + p - 2`
are both prime. For example `a(8) = 2` since 3 and 5 are the only primes `p ≤ 8` with `16 - p`
and `14 + p` both prime.

Conjecture (Zhi-Wei Sun, Nov 10 2012): `a(n) > 0` except for `n = 1, 2, 4, 6, 10, 22, 57`. The
entry notes that this is stronger than the Goldbach conjecture and that it has been verified for
`n` up to `5*10^7`.

Since `a(n)` counts the primes `p ≤ n` with `2n - p` and `2n + p - 2` prime, `a(n) > 0` says
exactly that such a prime exists. The statement is the equivalence, for every `n ≥ 1`: such a
prime exists if and only if `n` is not one of the seven listed exceptions. (At the seven
exceptions `a(n) = 0` is a finite computation; the open content is the other direction.) The
entry's further conjectures, with `p` in the interval `(n, 2n)`, are separate claims and are not
part of this statement.

Conventions: everything is in `ℕ`. The subtraction `2n - p` is exact because `p ≤ n`, and
`2n + p - 2` is exact because `n ≥ 1`.
-/

namespace OMA.S_oeis_a219026

theorem main :
    ∀ n : ℕ, 0 < n →
      ((∃ p : ℕ, p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (2 * n - p) ∧ Nat.Prime (2 * n + p - 2)) ↔
        n ∉ ({1, 2, 4, 6, 10, 22, 57} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a219026
