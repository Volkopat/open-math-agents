import Mathlib

/-!
# A030173: Differences p(i)-p(j) between primes, sorted in numerical order.

Source: https://oeis.org/A030173

The source conjectures (Polignac 1849) that this sequence is the union of the even
numbers and the odd primes minus 2.  Since the listed sequence starts at 1, the
universe of the statement is the positive integers.  Only the body of `main` is
`sorry`; all definitions below are complete.
-/

namespace OMA.S_oeis_a030173

/-- A positive integer is a difference of two primes. -/
def IsPrimeDifference (d : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p - q = d

/-- A positive integer is even or is an odd prime minus two. -/
def IsEvenOrOddPrimeMinusTwo (d : ℕ) : Prop :=
  Even d ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ p - 2 = d

theorem main :
    {d : ℕ | 0 < d ∧ IsPrimeDifference d} =
      {d : ℕ | 0 < d ∧ IsEvenOrOddPrimeMinusTwo d} := by
  sorry

end OMA.S_oeis_a030173
