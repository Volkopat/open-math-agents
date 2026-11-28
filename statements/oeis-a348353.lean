import Mathlib

/-!
# OEIS A348353: p^2+q+r, p+q^2+r, p+q+r^2 all prime (q, r the next two primes)

Source: https://oeis.org/A348353
Credit: @unserus

OEIS (Robert Israel, Oct 21 2021): "The generalized Bunyakovsky conjecture
implies that there are infinitely many terms, in fact infinitely many for which
q = p+2 and r = p+6."

The terms are the primes `p` such that, with `q` the next prime after `p` and
`r` the next prime after `q`, the numbers `p^2 + q + r`, `p + q^2 + r` and
`p + q + r^2` are all prime. "`b` is the next prime after `a`" is written
`IsNextPrime a b`: `b` is prime, `a < b`, and no prime lies strictly between.
The open statement is that the sequence is infinite.
-/

namespace OMA.S_oeis_a348353

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A348353. -/
def a348353Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q r, IsNextPrime p q ∧ IsNextPrime q r ∧
    (p ^ 2 + q + r).Prime ∧ (p + q ^ 2 + r).Prime ∧ (p + q + r ^ 2).Prime}

/-- A348353 is infinite. -/
theorem main : a348353Set.Infinite := by
  sorry

end OMA.S_oeis_a348353
