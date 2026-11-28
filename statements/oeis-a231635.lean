import Mathlib

/-!
# A231635: n = x + y with 0 < x ≤ y such that lcm(x, y) + 1 is prime

Source: https://oeis.org/A231635

A231635 (offset 1): `a(n)` is the number of ways to write `n = x + y` with `0 < x ≤ y` such that
`lcm(x, y) + 1` is prime. For example `a(9) = 1` since `9 = 3 + 6` with `lcm(3, 6) + 1 = 7`
prime.

Conjecture (Zhi-Wei Sun, Nov 12 2013):
(i) `a(n) > 0` for all `n > 1`. Also, any integer `n > 3` can be written as `x + y`
    (`x, y > 0`) with `lcm(x, y) - 1` prime.
(ii) Each `n = 2, 3, …` can be expressed as `x + y` (`x, y > 0`) with
    `lcm(x, y)^2 + lcm(x, y) + 1` prime. Also, any integer `n > 1` not equal to 10 can be written
    as `x + y` (`x, y > 0`) with `lcm(x, y)^2 + 1` prime.

The entry notes that both parts of (i) have been verified for `n` up to `10^9` and both parts of
(ii) for `n` up to `10^6` (Mauro Fiorentini, Aug 02 2023).

All four assertions are stated, as a conjunction in the order above. Since `a(n)` counts the
pairs `0 < x ≤ y` with `x + y = n` and `lcm(x, y) + 1` prime, the first assertion says exactly
that such a pair exists.

Conventions: everything is in `ℕ`, with `Nat.lcm`; `lcm(x, y) - 1` is an exact subtraction
because `lcm(x, y) ≥ 1` for positive `x`, `y`.
-/

namespace OMA.S_oeis_a231635

theorem main :
    (∀ n : ℕ, 1 < n →
      ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (Nat.lcm x y + 1)) ∧
    (∀ n : ℕ, 3 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime (Nat.lcm x y - 1)) ∧
    (∀ n : ℕ, 2 ≤ n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
        Nat.Prime (Nat.lcm x y ^ 2 + Nat.lcm x y + 1)) ∧
    (∀ n : ℕ, 1 < n → n ≠ 10 →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime (Nat.lcm x y ^ 2 + 1)) := by
  sorry

end OMA.S_oeis_a231635
