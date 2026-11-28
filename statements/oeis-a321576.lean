import Mathlib

/-!
# A321576: for composite n, 2^n - 1 has a divisor not congruent to 1 modulo n

Source: https://oeis.org/A321576

A321576 (offset 1): `a(n)` is the smallest `b > 1` such that `b^n - (b-1)^n` has all divisors
`d ≡ 1 (mod n)`: 2, 2, 2, 3, 2, 4, 2, 45, 3, 6, 2, 301, …  For example `a(6) = 4` since
`4^6 - 3^6 = 3367` has divisors 1, 7, 13, 37, 91, 259, 481, 3367, each congruent to 1 modulo 6,
and 4 is the smallest such `b`.

The entry notes that if `n` is prime, then `a(n) = 2`.

Conjecture (Thomas Ordowski, Nov 13 2018): if `n` is composite, then `a(n) > 2`.

Since `a(n)` is the smallest `b > 1` with the stated property, `a(n) > 2` means exactly that
`b = 2` does not have it, i.e. that `2^n - 1^n = 2^n - 1` has a divisor `d` that is not
congruent to `1` modulo `n`. The conjecture is stated in that form for every composite `n`.

Conventions: a composite number is an integer greater than `1` that is not prime. Everything is
in `ℕ`, the congruence is `Nat.ModEq`, and `2^n - 1` is an exact subtraction.
-/

namespace OMA.S_oeis_a321576

theorem main :
    ∀ n : ℕ, 1 < n → ¬ Nat.Prime n → ∃ d : ℕ, d ∣ 2 ^ n - 1 ∧ ¬ (d ≡ 1 [MOD n]) := by
  sorry

end OMA.S_oeis_a321576
