import Mathlib

/-!
# OEIS A298077: Oblong numbers that are the sum of 2 successive primes

Source: https://oeis.org/A298077
Credit: @unserus

OEIS: "Is this sequence infinite?" and (Robert Israel, Feb 11 2018): "Includes
all n*(n+1) for which n*(n+1)/2 - 2 and n*(n+1)/2 + 2 are prime. The generalized
Bunyakovsky conjecture implies there are infinitely many of these."

The terms are the oblong numbers `n * (n + 1)` (n ≥ 1) equal to `p + q` for a
prime `p` and the next prime `q` after `p`. The statement is the expected
answer to the question: the sequence is infinite.
-/

namespace OMA.S_oeis_a298077

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A298077. -/
def a298077Set : Set ℕ :=
  {m | (∃ n, 1 ≤ n ∧ m = n * (n + 1)) ∧ ∃ p q, p.Prime ∧ IsNextPrime p q ∧ m = p + q}

/-- A298077 is infinite. -/
theorem main : a298077Set.Infinite := by
  sorry

end OMA.S_oeis_a298077
