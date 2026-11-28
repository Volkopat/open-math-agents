import Mathlib

/-!
# A248593: Least positive integer m such that m + n divides F(m), where F(m) is the m-th Fibonacci number given by A000045.

Source: https://oeis.org/A248593
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248593 (Zhi-Wei Sun, Oct 09 2014): a(n) exists for any
n > 0. Moreover, a(n) <= n*(n-1) except for n = 1, 2, 3, 9.

Conventions:
* The sequence has offset 1 (data 10, 6, 84, 12, 16, 7, 27, 9, 144, 30, 28, 12, ...).
* `a n` is the least positive integer m such that m + n divides F(m) (`Nat.fib m`), as an infimum
  (`sInf`) over the natural numbers; `a(n) exists` is the statement that the set of such m is
  nonempty, and then the infimum is its least element.
* `a(n) <= n*(n-1) except for n = 1, 2, 3, 9` is rendered as: a(n) <= n*(n-1) for every n > 0
  other than 1, 2, 3, 9. (For n = 1, 2, 3, 9 the data gives a(n) > n*(n-1).)
* Both sentences are formalized, as a conjunction for each n > 0.
-/

namespace OMA.S_oeis_a248593

/-- A248593: least positive integer m such that m + n divides Fibonacci(m). -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ m + n ∣ Nat.fib m}

/-- The conjecture recorded in A248593. -/
theorem main : ∀ n : ℕ, 0 < n →
    ((∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.fib m) ∧
      (n ∉ ({1, 2, 3, 9} : Finset ℕ) → a n ≤ n * (n - 1))) := by
  sorry

end OMA.S_oeis_a248593
