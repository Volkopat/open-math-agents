import Mathlib

/-!
# Erdős–Mollin–Walsh conjecture

Source: https://en.wikipedia.org/wiki/Powerful_number#Mathematical_properties
Credit: @ihateSAS

## The problem

A natural number is *powerful* if every prime `p` dividing it satisfies `p ^ 2 ∣ n`.
The conjecture states that no three consecutive natural numbers are all powerful.
Pairs of consecutive powerful numbers do exist (`8` and `9`), so three is the first
open case; a run of four is impossible, because one of four consecutive numbers is
`2` modulo `4`, and `2` divides that number to the first power only.

## Formalization notes

* `Powerful` is not in Mathlib. It is defined here exactly as in
  `FormalConjecturesForMathlib/Data/Nat/Full.lean`, where it is `(2).Full`, i.e.
  every prime factor occurs with exponent at least two.
* The statement quantifies over all `n : ℕ`. Under this definition `0` is powerful
  vacuously (it has no prime factors) and `1` is powerful, but `2` is not, so the
  corner `n = 0` is not a counterexample.
-/

namespace OMA.S_wp_erdos_mollin_walsh_conjecture

/-- A natural number `n` is powerful if every prime factor `p` of `n` satisfies `p ^ 2 ∣ n`. -/
def Powerful (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

/-- No three consecutive natural numbers are all powerful. -/
theorem main : ¬ ∃ n : ℕ, Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) := by
  sorry

end OMA.S_wp_erdos_mollin_walsh_conjecture
