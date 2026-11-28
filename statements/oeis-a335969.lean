import Mathlib

/-!
# OEIS A335969: Sphenic numbers that are also the sum of three consecutive primes

Source: https://oeis.org/A335969
Credit: @unserus

OEIS (Robert Israel, Nov 24 2022): "Includes 15*p where p, 5*p-14, 5*p-2 and
5*p+16 are consecutive primes. Dickson's conjecture implies there are infinitely
many such terms."

A sphenic number (A007304) is a product of three distinct primes, i.e. a
squarefree number with exactly three prime factors. The terms are the sphenic
numbers of the form `prime(i) + prime(i+1) + prime(i+2)` (three consecutive
primes; `Nat.nth Nat.Prime i` is the `i`-th prime, 0-indexed). The open
statement is that the sequence is infinite.
-/

namespace OMA.S_oeis_a335969

/-- `m` is sphenic: squarefree with exactly three distinct prime factors. -/
def IsSphenic (m : ℕ) : Prop := Squarefree m ∧ m.primeFactors.card = 3

/-- The terms of A335969. -/
def a335969Set : Set ℕ :=
  {m | IsSphenic m ∧ ∃ i, m = Nat.nth Nat.Prime i + Nat.nth Nat.Prime (i + 1) +
    Nat.nth Nat.Prime (i + 2)}

/-- A335969 is infinite. -/
theorem main : a335969Set.Infinite := by
  sorry

end OMA.S_oeis_a335969
