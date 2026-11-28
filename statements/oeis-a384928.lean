import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Divisors

namespace OMA.S_oeis_a384928

/-- The `n`-th triangular number `T(n) = n * (n + 1) / 2`. -/
def tri (n : ℕ) : ℕ :=
  n * (n + 1) / 2

/-- The sorted list of positive divisors of `m`. -/
def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

/-- The number of 2-dense sublists of divisors of `m`: when the positive divisors of `m` are
listed in increasing order `d_0 < d_1 < ... < d_{r-1}`, a 2-dense sublist is a maximal
contiguous block in which each term is at most twice the previous term. For `m ≥ 1`, this
equals `1` plus the number of indices `i` with `d_{i+1} > 2 * d_i`. -/
def numTwoDenseSublists (m : ℕ) : ℕ :=
  let ds := sortedDivisors m
  if ds.isEmpty then 0
  else 1 + ((List.range (ds.length - 1)).filter (fun i =>
    2 * ds.getD i 0 < ds.getD (i + 1) 0)).length

/-- `a(n)` (OEIS A384928): the number of 2-dense sublists of divisors of the `n`-th
triangular number `T(n) = n * (n + 1) / 2`. -/
def a (n : ℕ) : ℕ :=
  numTwoDenseSublists (tri n)

/-- Conjecture (OEIS A384928): all odd-indexed terms `a(2k + 1)` are odd. -/
theorem main : ∀ k : ℕ, Odd (a (2 * k + 1)) := by
  sorry

end OMA.S_oeis_a384928
