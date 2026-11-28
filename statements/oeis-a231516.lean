import Mathlib

/-!
# A231516: n = x + y with 0 < x ≤ y such that x!*y + 1 is prime

Source: https://oeis.org/A231516

A231516 (offset 1): `a(n)` is the number of ways to write `n = x + y` with `0 < x ≤ y` such that
`x!*y + 1` is prime. For example `a(9) = 1` since `9 = 3 + 6` with `3!*6 + 1 = 37` prime.

Conjecture (Zhi-Wei Sun, Nov 11 2013): `a(n) > 0` for all `n > 1`. Also, any integer `n > 3` can
be written as `x + y` with `0 < x ≤ y` such that `x!*y - 1` is prime. The entry notes that the
conjecture has been verified for `n` up to `10^6`.

Both sentences of the conjecture are stated, as a conjunction. Since `a(n)` counts the pairs
`0 < x ≤ y` with `x + y = n` and `x!*y + 1` prime, the first sentence says exactly that such a
pair exists.

Conventions: everything is in `ℕ`; `x! * y - 1` is an exact subtraction because `x!*y ≥ 1` for
`y ≥ x > 0`.
-/

namespace OMA.S_oeis_a231516

theorem main :
    (∀ n : ℕ, 1 < n →
      ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x.factorial * y + 1)) ∧
    (∀ n : ℕ, 3 < n →
      ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x.factorial * y - 1)) := by
  sorry

end OMA.S_oeis_a231516
