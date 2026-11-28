import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Denominators of partial sums of the scaled Catalan numbers

The partial sum starts with C(1) and ends with C(n). The index formula
for A283208 uses the finite floor sum given in that sequence's entry.
These are the two conjectures of Groux Roland and Alexander Staunton.

Sources: https://oeis.org/A120069 and https://oeis.org/A283208
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a120069

def term (n : ℕ) : ℚ := (catalan n : ℚ) / 4 ^ (n - 1)

def partialSum (n : ℕ) : ℚ := ∑ j ∈ Finset.range n, term (j + 1)

def a283208 (n : ℕ) : ℕ := n +
  ∑ j ∈ Finset.Ico 1 (Nat.log 2 (n + 1) + 1), (n + 1) / 2 ^ j

theorem main : ∀ n : ℕ, 1 ≤ n →
    (partialSum n).den = (term n).den ∧
    (partialSum n).den = 2 ^ (a283208 n - 2) := by
  sorry

end OMA.S_oeis_a120069
