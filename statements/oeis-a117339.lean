import Mathlib

/-!
# A117339: Eventual periodicity for a modified Fibonacci recurrence

Source: https://oeis.org/A117339

Add the two preceding terms. Keep a prime sum, and divide a composite sum by its
largest prime factor once. The conjecture allows any two positive initial terms.
The Lean sequence starts at index zero, corresponding to index one in the OEIS entry.
-/

namespace OMA.S_oeis_a117339

/-- For a composite sum, the last entry of the sorted factor list is its largest prime factor.
Positive initial terms ensure that every sum is at least two. -/
def reduceSum (sum : ℕ) : ℕ :=
  if sum.Prime then sum else sum / (sum.primeFactorsList.getLastD 1)

/-- The recurrence starting with `first` and `second` at indices zero and one. -/
def term (first second : ℕ) : ℕ → ℕ
  | 0 => first
  | 1 => second
  | n + 2 => reduceSum (term first second n + term first second (n + 1))

theorem main :
    ∀ first second : ℕ, 0 < first → 0 < second →
      ∃ start period : ℕ, 0 < period ∧
        ∀ n ≥ start, term first second (n + period) = term first second n := by
  sorry

end OMA.S_oeis_a117339
