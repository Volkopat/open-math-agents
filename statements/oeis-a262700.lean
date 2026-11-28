import Mathlib

/-!
# A262700: Primes p such that pi(p^2)*pi(q^2) is a square for some prime q < p, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A262700
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A262700):
(i) The sequence has infinitely many terms.
(ii) The Diophantine equation `pi(x^n) * pi(y^n) = z^n` with `n > 2` and `x, y, z > 0` has no
solution.

Conventions: `pi(x)` is `Nat.primeCounting x`, the number of primes `≤ x`. "Is a square" means
`IsSquare`, i.e. equal to `m * m` for some natural number `m`. The sequence lists the primes `p`
for which some prime `q < p` makes `pi(p^2) * pi(q^2)` a square; part (i) says that this set is
infinite. In part (ii), `n`, `x`, `y`, `z` are positive integers with `n > 2`, taken in `ℕ`.
-/

namespace OMA.S_oeis_a262700

/-- The terms of A262700. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ q < p ∧
    IsSquare (Nat.primeCounting (p ^ 2) * Nat.primeCounting (q ^ 2))}

/-- Sun's conjecture in A262700: (i) the sequence is infinite, and (ii) the equation
`pi(x^n) * pi(y^n) = z^n` has no solution with `n > 2` and `x, y, z > 0`. -/
theorem main :
    S.Infinite ∧
      ∀ n x y z : ℕ, 2 < n → 0 < x → 0 < y → 0 < z →
        Nat.primeCounting (x ^ n) * Nat.primeCounting (y ^ n) ≠ z ^ n := by
  sorry

end OMA.S_oeis_a262700
