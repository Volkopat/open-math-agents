import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Lattice.Nat

/-!
# Triangular differences, first appearances, and consecutive partitions

A212652 takes the least positive upper triangular index M. A141419
uses a column index c in 1,...,M, and A209260 removes values present in
any earlier row. A partition into consecutive positive parts is specified
by its least and greatest part, each integer in the interval appearing once.

Sources: https://oeis.org/A212652, https://oeis.org/A141419, and
https://oeis.org/A209260 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a212652

def tri (m : ℕ) : ℕ := ∑ j ∈ Finset.range (m + 1), j

def admissible (n m : ℕ) : Prop := 0 < m ∧ ∃ k ≤ m, n = tri m - tri k

noncomputable def a (n : ℕ) : ℕ := sInf {m | admissible n m}

def rawRow (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).image fun c => tri m - tri (m - c)

def freshRow (m : ℕ) : Finset ℕ := rawRow m \ (Finset.range m).biUnion rawRow

def largestParts (n : ℕ) : Set ℕ :=
  {m | ∃ l, 0 < l ∧ l ≤ m ∧ (∑ j ∈ Finset.Icc l m, j) = n}

theorem main : ∀ n : ℕ, 0 < n →
    n ∈ freshRow (a n) ∧ IsLeast (largestParts n) (a n) := by
  sorry

end OMA.S_oeis_a212652
