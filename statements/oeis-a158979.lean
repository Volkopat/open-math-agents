import Mathlib

/-!
# A158979: smallest m > n such that n^4 + m^4 is prime

Source: https://oeis.org/A158979

A158979 (offset 1): `a(n)` is the smallest number `> n` such that `n^4 + a(n)^4` is prime:
2, 3, 4, 5, 8, 7, 10, 9, 10, 13, …  For example `1^4 + 2^4 = 17` is prime, so `a(1) = 2`, and
`2^4 + 3^4 = 97` is prime, so `a(2) = 3`.

The entry (Ulrich Krug, Apr 01 2009) states two conjectures:
1. `a(n)` exists for all `n`, i.e., the sequence is well-defined and infinite.
2. `a(n) - n = 1` for infinitely many `n`.

Both are stated, as a conjunction.

Conventions:
- `a(n)` exists exactly when some `m > n` has `n^4 + m^4` prime, so the first conjecture is
  stated as the existence of such an `m` for every `n ≥ 1` (offset 1).
- `a(n) = n + 1` means that `n^4 + (n+1)^4` is prime, so the second conjecture says that the set
  of such `n` is infinite.
-/

namespace OMA.S_oeis_a158979

theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, n < m ∧ Nat.Prime (n ^ 4 + m ^ 4)) ∧
    Set.Infinite {n : ℕ | Nat.Prime (n ^ 4 + (n + 1) ^ 4)} := by
  sorry

end OMA.S_oeis_a158979
