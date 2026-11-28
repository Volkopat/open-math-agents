import Mathlib

/-!
# A231903: even numbers that are the sum of two different primes `> 3` in exactly one way

Source: https://oeis.org/A231903
Credit: @Lenqth

A231903 lists the even numbers `n` that can be written as `n = p + q` with `p < q` both prime and
`p, q > 3` in exactly one way. The listed terms are `12, 16, 20, 22, 26, 32, 38, 62`
(`12 = 5 + 7`, ..., `62 = 19 + 43`).

Formalizes the conjecture in the comments of A231903: there are no more numbers `> 62` in the
sequence, i.e. the sequence is exactly `{12, 16, 20, 22, 26, 32, 38, 62}`. A representation is
counted by its smaller part `p`, with `3 < p < n - p` and `p`, `n - p` prime (as in the PARI program
of the entry, which runs over primes `5 ≤ p ≤ n/2 - 1`).
-/

namespace OMA.S_oeis_a231903

/-- The number of ways to write `n = p + q` with `p < q` both prime and `p > 3`. -/
def numReps (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => 3 < p ∧ p < n - p ∧ p.Prime ∧ (n - p).Prime)).card

/-- The even numbers with exactly one such representation are exactly
`12, 16, 20, 22, 26, 32, 38, 62`. -/
theorem main : {n : ℕ | Even n ∧ numReps n = 1} = {12, 16, 20, 22, 26, 32, 38, 62} := by
  sorry

end OMA.S_oeis_a231903
