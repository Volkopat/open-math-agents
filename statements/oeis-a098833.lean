import Mathlib

/-!
# A098833: Numbers n such that the sum of primes dividing n (with repetition) is a Fibonacci number.

Source: https://oeis.org/A098833
Credit: @gblacher2

The sum of the primes dividing `n`, with repetition, is `sopfr(n) = A001414(n)`, which is
`n.primeFactorsList.sum` in Mathlib. `sopfr(1) = 0 = F(0)`, so `1` is a term, as in the OEIS data.
The conjecture in the entry: there are infinitely many consecutive terms in this sequence, read as
infinitely many `n` such that `n` and `n + 1` are both terms (for example `143335` and `143336`).
-/

namespace OMA.S_oeis_a098833

/-- `n` is a term of A098833: `n > 0` and the sum of the primes dividing `n`, counted with
repetition, is a Fibonacci number. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, Nat.fib k = n.primeFactorsList.sum

/-- There are infinitely many consecutive terms `n`, `n + 1` in A098833. -/
theorem main : {n : ℕ | IsTerm n ∧ IsTerm (n + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a098833
