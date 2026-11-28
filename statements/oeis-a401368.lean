import Mathlib

/-!
# A401368: even numbers as a twin prime plus a cousin prime

Source: https://oeis.org/A401368

A401368 (offset 1): `a(n)` is the number of ways to write `2n` as `p + q` with `p` a twin prime
and `q` a cousin prime: 0, 0, 1, 1, 2, 1, 3, 3, 3, 4, …  Here a twin prime is a prime `p` with
`p-2` or `p+2` prime (A001097), and a cousin prime is a prime `q` with `q-4` or `q+4` prime
(A023200, A046132). For example `a(15) = 5`:
`30 = 7 + 23 = 11 + 19 = 13 + 17 = 17 + 13 = 19 + 11`.

Conjecture (Ali Ashter, Oct 23 2026): `a(n) > 0` for all `n > 2`, i.e., every even number
greater than 4 is the sum of a twin prime and a cousin prime. The entry notes that this has been
verified for `2n ≤ 3.4*10^10`.

The conjecture is stated in the entry's own i.e. form: existence of a twin prime `p` and a cousin
prime `q` with `p + q = 2n`.

Conventions: everything is in `ℕ`. The truncated subtractions are harmless: `p - 2` is truncated
only for `p < 2`, where `p` is not prime, and for a prime `q < 4` the truncated `q - 4 = 0` is
not prime, just as the negative integer `q - 4` is not a prime.
-/

namespace OMA.S_oeis_a401368

/-- A twin prime (A001097): a prime `p` with `p - 2` or `p + 2` prime. -/
def IsTwinPrime (p : ℕ) : Prop := Nat.Prime p ∧ (Nat.Prime (p - 2) ∨ Nat.Prime (p + 2))

/-- A cousin prime: a prime `q` with `q - 4` or `q + 4` prime. -/
def IsCousinPrime (q : ℕ) : Prop := Nat.Prime q ∧ (Nat.Prime (q - 4) ∨ Nat.Prime (q + 4))

theorem main :
    ∀ n : ℕ, 2 < n → ∃ p q : ℕ, IsTwinPrime p ∧ IsCousinPrime q ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a401368
