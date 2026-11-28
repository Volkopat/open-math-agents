import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Multiples of three among the A123722 square-residue counts

A123722 enumerates the positive m for which the number of distinct
squares modulo m is ceil((m+1)/3). In the first assertion the one-based
index exceeds two, equivalently the list has at least two earlier values.
The second assertion says every odd prime p occurs as the quotient
of the qualifying value 3p.

Sources: https://oeis.org/A123722 and https://oeis.org/A000224
(OEIS Foundation, CC BY-SA 4.0). Credit: @Solitude1312
-/

namespace OMA.S_oeis_a123722

def squares (m : ℕ) : Finset ℕ := (Finset.range m).image fun k => k ^ 2 % m

def qualifies (m : ℕ) : Prop := 0 < m ∧ (squares m).card = (m + 3) / 3

noncomputable def preceding (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico 1 m).filter qualifies).card

theorem main :
    (∀ m : ℕ, qualifies m → 2 ≤ preceding m → 3 ∣ m → (m / 3).Prime) ∧
    (∀ p : ℕ, p.Prime → Odd p → qualifies (3 * p)) := by
  sorry

end OMA.S_oeis_a123722
