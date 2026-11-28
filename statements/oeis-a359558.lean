import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Card

/-!
# Five distinct Fibonacci summands

Source: Robert Israel, OEIS A359558, https://oeis.org/A359558 (CC BY-SA 4.0).
Credit: @jatin6

The six published terms give the least integers with respectively one through
six representations. The conjecture that there are no further terms says that
no integer has more than six representations. A representation lists indices
in strictly decreasing order. Index i denotes F_(i+2), so 1 appears only once.
-/

namespace OMA.S_oeis_a359558

def weight (i : ℕ) := Nat.fib (i + 2)

def Represents (n : ℕ) (l : List ℕ) : Prop :=
  l.Pairwise (· > ·) ∧ l.length = 5 ∧ (l.map weight).sum = n

theorem main : ∀ (n : ℕ) (s : Finset (List ℕ)),
    (∀ l ∈ s, Represents n l) → s.card ≤ 6 := by
  sorry

end OMA.S_oeis_a359558
