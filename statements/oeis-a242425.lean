import Mathlib

/-!
# A242425: a square k^2 < p whose inverse modulo p is a prime below p

Source: https://oeis.org/A242425

A242425 (offset 1): `a(n)` is the number of squares `k^2 < prime(n)` with
`k^2*p ≡ 1 (mod prime(n))` for some prime `p < prime(n)`: 0, 0, 0, 1, 2, 1, 2, 2, 1, 2, …  For
example `a(4) = 1` since `2^2*2 ≡ 1 (mod 7)`, and `a(6) = 1` since `3^2*3 ≡ 1 (mod 13)`.

Conjecture (Zhi-Wei Sun, May 13 2014): `a(n) > 0` for all `n > 3`. In other words, for any prime
`p > 5`, there exists a positive square `k^2 < p` such that the inverse of `k^2` mod `p` among
`1, …, p-1` is prime. The entry notes that this has been verified for all `n = 4, …, 10^7`.

The conjecture is stated in the entry's own in-other-words form (`n > 3` is the same as
`prime(n) > 5`, since `prime(3) = 5`): there are `k > 0` with `k^2 < p` and a prime `q < p` with
`k^2*q ≡ 1 (mod p)`; such a `q` is exactly the inverse of `k^2` among `1, …, p-1`.

Conventions: everything is in `ℕ`, and the congruence is `Nat.ModEq`.
-/

namespace OMA.S_oeis_a242425

theorem main :
    ∀ p : ℕ, Nat.Prime p → 5 < p →
      ∃ k q : ℕ, 0 < k ∧ k ^ 2 < p ∧ Nat.Prime q ∧ q < p ∧ k ^ 2 * q ≡ 1 [MOD p] := by
  sorry

end OMA.S_oeis_a242425
