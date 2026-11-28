import Mathlib

/-!
# OEIS A358922: four consecutive primes p, q, r, s with q*s - p*r a square

Source: https://oeis.org/A358922
Credit: @unserus

OEIS: "If, for example, 3*x^2-11, 3*x^2-5, 3*x^2+5 and 3*x^2+11 are consecutive
primes, then 3*x^2-11 is a term. According to the generalized Bunyakovsky
conjecture there should be infinitely many such terms."

The terms are the primes `p` such that, with `q, r, s` the next three primes
after `p`, `q * s - p * r` is a perfect square (it is positive, since `p < q`
and `r < s`, so the subtraction in `ℕ` does not truncate). The open statement
is that the sequence is infinite.
-/

namespace OMA.S_oeis_a358922

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A358922. -/
def a358922Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q r s, IsNextPrime p q ∧ IsNextPrime q r ∧ IsNextPrime r s ∧
    IsSquare (q * s - p * r)}

/-- A358922 is infinite. -/
theorem main : a358922Set.Infinite := by
  sorry

end OMA.S_oeis_a358922
