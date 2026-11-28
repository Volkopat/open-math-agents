import Mathlib

/-!
# A263979: least prime of the form a^2 + b^2 with a > n and b > n

Source: https://oeis.org/A263979

A263979 (offset 0): `a(n)` is the least prime `p` of the form `p = a^2 + b^2` with `a > n` and
`b > n`: 2, 13, 41, 41, 61, 113, 113, 181, 181, 269, …  For example the smallest prime of the
form `a^2 + b^2` with `a > 2` and `b > 2` is `41 = 4^2 + 5^2`, so `a(2) = 41`. The entry notes
that `a(n)` exists for every `n` (Sierpinski, Elementary Theory of Numbers, 1988, p. 221).

Conjecture (Jonathan Sondow, Nov 09 2015): `a(n) ≤ 2*(2n+1)^2` for all `n ≥ 0`.

Since `a(n)` is the least prime of the form `a^2 + b^2` with `a > n` and `b > n`, the bound
`a(n) ≤ 2*(2n+1)^2` holds exactly when some prime of that form is at most `2*(2n+1)^2`, and the
conjecture is stated in that form.

Conventions: everything is in `ℕ`, and `n` ranges over all of `ℕ` (offset 0). The variables are
named `x`, `y` to avoid a clash with the sequence name.
-/

namespace OMA.S_oeis_a263979

theorem main :
    ∀ n : ℕ, ∃ x y : ℕ, n < x ∧ n < y ∧ Nat.Prime (x ^ 2 + y ^ 2) ∧
      x ^ 2 + y ^ 2 ≤ 2 * (2 * n + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a263979
