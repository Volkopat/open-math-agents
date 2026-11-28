import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Square residues at multiples of four

A123723 lists, in increasing order starting at index one, exactly the
positive m for which the number of distinct squares modulo m equals
ceil((m+1)/4). The number of previous qualifying m's gives the exact
index condition in Layman's conjecture: n>4 means at least four
earlier positive values.

Sources: https://oeis.org/A123723 and https://oeis.org/A000224
(OEIS Foundation, CC BY-SA 4.0). Credit: @Solitude1312
-/

namespace OMA.S_oeis_a123723

def squares (m : ℕ) : Finset ℕ := (Finset.range m).image fun k => k ^ 2 % m

def qualifies (m : ℕ) : Prop := 0 < m ∧ (squares m).card = (m + 4) / 4

noncomputable def preceding (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico 1 m).filter qualifies).card

theorem main : ∀ m : ℕ, qualifies m → 4 ≤ preceding m → 4 ∣ m → (m / 4).Prime := by
  sorry

end OMA.S_oeis_a123723
