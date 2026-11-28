import Mathlib

/-!
# OEIS A387863: two integers between consecutive primes p < q with all prime factors < q - p

Source: https://oeis.org/A387863
Credit: @unserus

OEIS: "Erdős (1976) conjectured that there are infinitely many primes with this
property, but this remains unsolved."

The terms are the primes `p` such that, with `q` the next prime after `p`, at
least two integers `n` with `p < n < q` have all their prime factors less than
`q - p`. (Example: for 7 and 11, the numbers 8 = 2^3 and 9 = 3^2 have all prime
factors below 4.) The conjecture is that there are infinitely many such `p`.
-/

namespace OMA.S_oeis_a387863

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A387863. -/
def a387863Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q, IsNextPrime p q ∧
    2 ≤ ((Finset.Ioo p q).filter fun n => ∀ r ∈ n.primeFactors, r < q - p).card}

/-- A387863 is infinite. -/
theorem main : a387863Set.Infinite := by
  sorry

end OMA.S_oeis_a387863
