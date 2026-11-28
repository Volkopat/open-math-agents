import Mathlib

/-!
# A229166: n = x(x+1)/2 + y with y(y+1)/2 + 1 prime

Source: https://oeis.org/A229166

A229166 (offset 1): `a(n)` is the number of ordered ways to write `n = x*(x+1)/2 + y` with
`y*(y+1)/2 + 1` prime, where `x` and `y` are nonnegative integers. For example `a(6) = 1` since
`6 = 2*3/2 + 3` with `3*4/2 + 1 = 7` prime, and `a(60) = 1` since `60 = 0*1/2 + 60` with
`60*61/2 + 1 = 1831` prime.

Conjecture (Zhi-Wei Sun, Oct 15 2013): `a(n) > 0` for all `n > 0`. Moreover, if `n > 0` is not
among 1, 3, 60, then there are positive integers `x` and `y` with `x*(x+1)/2 + y = n` such that
`y*(y+1)/2 + 1` is prime.

Both sentences of the conjecture are stated, as a conjunction. Since `a(n)` counts the pairs
`(x, y)` of nonnegative integers with `x*(x+1)/2 + y = n` and `y*(y+1)/2 + 1` prime, the first
sentence says exactly that such a pair exists.

Conventions: `x` and `y` range over `ℕ` (nonnegative integers) in the first part and are
required to be positive in the second part. The divisions by 2 are natural-number divisions and
are exact, because `x*(x+1)` and `y*(y+1)` are even.
-/

namespace OMA.S_oeis_a229166

theorem main :
    (∀ n : ℕ, 0 < n →
      ∃ x y : ℕ, x * (x + 1) / 2 + y = n ∧ Nat.Prime (y * (y + 1) / 2 + 1)) ∧
    (∀ n : ℕ, 0 < n → n ∉ ({1, 3, 60} : Finset ℕ) →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x * (x + 1) / 2 + y = n ∧
        Nat.Prime (y * (y + 1) / 2 + 1)) := by
  sorry

end OMA.S_oeis_a229166
