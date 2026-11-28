import Mathlib

/-!
# A248982: Sequence of distinct least positive numbers such that the average of the first n terms is a
Fibonacci number.

Source: https://oeis.org/A248982. Related: https://oeis.org/A000045 (Fibonacci numbers)
Credit: @Squee451

Data (offset 1): 1, 3, 2, 6, 13, 5, 26, 8, 53, 93, 21, 177, 34, 328, 55, 599, 89, 1079, 144, 1924, 233, ...

The entry's formula lines:
* Conjecture: a(n) = 2*a(n-2)+a(n-4)-2*a(n-6)-a(n-8) for n > 17. (Colin Barker, 19 October 2014)
* Conjecture: For n > 4, a(2*n+1) = A000045(n+3).

Conventions.
* `IsSeq a` says that `a : ℕ → ℕ` (indices from 1; the value at 0 is irrelevant) satisfies the
  definition: for every `n ≥ 1`, `a n` is the least positive integer `y` that is different from all
  earlier terms and for which `a 1 + ... + a (n-1) + y` equals `n` times a Fibonacci number
  (`Nat.fib`, with F(0) = 0, F(1) = F(2) = 1).
* The statement asserts that such a sequence exists and that both conjectures hold for every such
  sequence (it is unique on positive indices). The recurrence is written over the integers.
-/

namespace OMA.S_oeis_a248982

/-- `y` may be chosen as the `n`-th term: positive, unused, and the average of the first `n` terms
becomes a Fibonacci number. -/
def Eligible (a : ℕ → ℕ) (n y : ℕ) : Prop :=
  0 < y ∧ (∀ m, 1 ≤ m → m < n → a m ≠ y) ∧
    ∃ j : ℕ, (∑ m ∈ Finset.Ico 1 n, a m) + y = n * Nat.fib j

/-- `a` is the sequence A248982 on positive indices. -/
def IsSeq (a : ℕ → ℕ) : Prop := ∀ n, 1 ≤ n → IsLeast {y : ℕ | Eligible a n y} (a n)

theorem main :
    (∃ a : ℕ → ℕ, IsSeq a) ∧
    ∀ a : ℕ → ℕ, IsSeq a →
      (∀ n : ℕ, 17 < n → (a n : ℤ) = 2 * a (n - 2) + a (n - 4) - 2 * a (n - 6) - a (n - 8)) ∧
      (∀ n : ℕ, 4 < n → a (2 * n + 1) = Nat.fib (n + 3)) := by
  sorry

end OMA.S_oeis_a248982
