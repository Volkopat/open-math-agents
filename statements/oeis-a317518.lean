import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card

/-!
# OEIS A317518

These are the highly composite numbers whose difference from the next
square, counting the number itself when it is square, is also a square.
The sequence starts at index one and is in increasing order.

Source: https://oeis.org/A317518
-/

namespace OMA.S_oeis_a317518

/-- Highly composite numbers are strict records of the divisor count among
positive integers. The first such number is one. -/
def HighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → m.divisors.card < n.divisors.card

/-- The defining square condition includes the possibility of a zero gap. -/
def terms : Set ℕ := {n | HighlyComposite n ∧
  ∃ d : ℕ, (⌈Real.sqrt (n : ℝ)⌉₊) ^ 2 = n + d ^ 2}

/-- Schoenfield's conjecture states both the index and the value of the final term. -/
theorem main : terms.ncard = 120 ∧ IsGreatest terms 7675044034503567507122937600 := by
  sorry

end OMA.S_oeis_a317518
