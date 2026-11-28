import Mathlib

/-!
# A262730: Primes p such that p^2 = pi(x^3) + pi(y^3) for some positive integers x and y, where pi(m) denotes the number of primes not exceeding m.

Source: https://oeis.org/A262730
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A262730):
(i) The sequence has infinitely many terms.
(ii) There are infinitely many primes `p` such that `p^2 = pi(x^3 + y^3)` for some positive
integers `x` and `y`.

Conventions: `pi(m)` is `Nat.primeCounting m`, the number of primes `≤ m`. The positive integers
`x` and `y` are natural numbers with `0 < x` and `0 < y`. `S` is the set of terms of A262730 and
`T` is the set of primes in part (ii); the conjecture says that both sets are infinite.
-/

namespace OMA.S_oeis_a262730

/-- The terms of A262730: primes `p` with `p^2 = pi(x^3) + pi(y^3)` for some `x, y > 0`. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
    p ^ 2 = Nat.primeCounting (x ^ 3) + Nat.primeCounting (y ^ 3)}

/-- The primes of part (ii): primes `p` with `p^2 = pi(x^3 + y^3)` for some `x, y > 0`. -/
def T : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ p ^ 2 = Nat.primeCounting (x ^ 3 + y ^ 3)}

/-- Sun's conjecture in A262730: (i) the sequence has infinitely many terms, and (ii) there are
infinitely many primes `p` with `p^2 = pi(x^3 + y^3)` for some positive integers `x` and `y`. -/
theorem main : S.Infinite ∧ T.Infinite := by
  sorry

end OMA.S_oeis_a262730
