import Mathlib

/-!
# OEIS A351579: Primes p such that p plus the next two primes is a product of two consecutive primes

Source: https://oeis.org/A351579
Credit: @unserus

OEIS: "The Generalized Bunyakovsky Conjecture implies that, for example, there are
infinitely many terms of the form 12*s^2+12*s-1 where the next two primes are
12*s^2+12*s+1 and 12*s^2+12*s+5 and the sum of these is (6*s+1)*(6*s+5)."

The terms are the primes `p` such that, with `q` the next prime after `p` and
`r` the next prime after `q`, `p + q + r = s * t` for a prime `s` and the next
prime `t` after `s` (A006094). The open statement is that the sequence is
infinite.
-/

namespace OMA.S_oeis_a351579

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A351579. -/
def a351579Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q r, IsNextPrime p q ∧ IsNextPrime q r ∧
    ∃ s t, s.Prime ∧ IsNextPrime s t ∧ p + q + r = s * t}

/-- A351579 is infinite. -/
theorem main : a351579Set.Infinite := by
  sorry

end OMA.S_oeis_a351579
