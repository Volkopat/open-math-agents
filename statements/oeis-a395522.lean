import Mathlib.Data.Nat.Fib.Basic

/-!
# Eventual constancy of the periods of iterated Fibonacci functions

In OEIS A395522 (Jianing Song), the entry in row m and column k is the
least positive input period of the m-fold Fibonacci function modulo k.
Both row and column numbering begin at one, and the input runs over the
nonnegative integers, starting with F(0) = 0 and F(1) = 1.
The conjecture asks for a single least period for every sufficiently late
row of each fixed column.

Source: https://oeis.org/A395522
-/

namespace OMA.S_oeis_a395522

/-- Apply the Fibonacci function m times to the input x. -/
def iterFib : ℕ → ℕ → ℕ
  | 0, x => x
  | m + 1, x => Nat.fib (iterFib m x)

/-- Shifting the input by t leaves every value unchanged modulo k. -/
def isPeriod (m k t : ℕ) : Prop :=
  ∀ x : ℕ, iterFib m (x + t) % k = iterFib m x % k

theorem main : ∀ k : ℕ, 0 < k → ∃ N t : ℕ, 0 < N ∧ 0 < t ∧
    ∀ m : ℕ, N ≤ m → isPeriod m k t ∧
      ∀ s : ℕ, 0 < s → isPeriod m k s → t ≤ s := by
  sorry

end OMA.S_oeis_a395522
