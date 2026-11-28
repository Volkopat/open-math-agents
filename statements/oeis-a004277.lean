import Mathlib

/-!
# OEIS A004277: 1 together with positive even numbers.

Source: https://oeis.org/A004277
Credit: @unserus

The OEIS entry states: "Conjecturally, the differences of two consecutive primes
(without repetition)." That is, the distinct values of `prime(n+1) - prime(n)`,
listed in increasing order, are exactly the terms of A004277: `1, 2, 4, 6, 8, ...`.
Since A004277 is strictly increasing, this is the set equality stated below.
The value `1` comes from the gap `3 - 2`; the content of the conjecture is that every
positive even number occurs as a gap between consecutive primes.
-/

namespace OMA.S_oeis_a004277

/-- The terms of A004277, as a set: `1` together with the positive even numbers. -/
def a004277Set : Set ℕ := {1} ∪ {n : ℕ | 0 < n ∧ Even n}

/-- The difference of two consecutive primes, `prime(n+1) - prime(n)`, with the first prime
(`2`) at index zero. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The differences of two consecutive primes, without repetition, are exactly the terms of
A004277. -/
theorem main : Set.range primeGap = a004277Set := by
  sorry

end OMA.S_oeis_a004277
