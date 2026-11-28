import Mathlib

/-!
# A161682: Primes that are not of the form x^3 - y^2

Source: https://oeis.org/A161682

Conjecture (OEIS A161682):
There are infinitely many primes `p` that cannot be represented in the form `x^3 - y^2`
for integers `x, y` (equivalently `x, y : ℕ`, since `x^3 = p + y^2 > 0` forces `x > 0`).

Conventions:
- Offset: `1`; first terms: `3, 5, 17, 29, 31, 37, 41, 43, 59, 73, 97, ...`.
- We express the representation in `ℤ` as `∃ x y : ℤ, (p : ℤ) = x ^ 3 - y ^ 2`.
-/

namespace OMA.S_oeis_a161682

/-- The set of primes not representable as `x^3 - y^2` with `x, y : ℤ` (OEIS A161682). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ¬ ∃ x y : ℤ, (p : ℤ) = x ^ 3 - y ^ 2}

/-- Conjecture: there are infinitely many primes not of the form `x^3 - y^2`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a161682
